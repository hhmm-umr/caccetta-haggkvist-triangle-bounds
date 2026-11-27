#!/usr/bin/env python3
"""Compile a rational six-vertex dual into typed Lean instructions and kernel checks."""

import argparse
import itertools
import json
import math
import re
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

from exact_certificate import gram_matrix, integer, require
from verify_six_vertex import decode, flag_ids


def labeled_entries(family, values):
    k, _, size, _, flags = family
    require(len(flags) == len(values), "flag dimension mismatch")
    orders = [tuple(range(k)) + p for p in itertools.permutations(range(k, size))]
    result = {}
    for graph_code, value in zip(flags, values):
        if value == 0:
            continue
        graph = decode(size, graph_code)
        words = set()
        for order in orders:
            word = 0
            for j in range(1, size):
                word = 3**j * word + sum(graph[order[i]][order[j]]*3**i for i in range(j))
            words.add(word)
        for word in words:
            require(word not in result, "ambiguous flag index")
            result[word] = value
    return result


def zigzag(n):
    return 2*n if n >= 0 else -2*n-1


class Source:
    def __init__(self, out, namespace, imports):
        self.path = out
        self.namespace = namespace
        self.parts = ["module", "", *("public import " + n for n in imports),
                      "", "@[expose] public section", "", "namespace " + namespace, ""]

    def add(self, text):
        self.parts.extend((text, ""))

    def finish(self):
        self.parts.extend(("end " + self.namespace, ""))
        content = "\n".join(self.parts).encode()
        if not self.path.exists() or self.path.read_bytes() != content:
            self.path.write_bytes(content)

    def table(self, name, entries, signed=False):
        data = {k: zigzag(v) if signed else v for k, v in entries.items() if v}
        require(all(k >= 0 and v >= 0 for k, v in data.items()), "invalid table cell")
        start = min(data, default=0)
        width = max((v.bit_length() for v in data.values()), default=1)
        pages = defaultdict(int)
        for key, value in data.items():
            page, digit = divmod(key-start, 16)
            pages[page] |= value << (digit*width)
        root = self.tree(name, pages)
        self.add(f"def {name} : PackedTable := ⟨{start}, {width}, {hex((1 << width)-1)}, {root}⟩")

    def tree(self, name, items):
        nodes = 0

        def render(items):
            nonlocal nodes
            if not items:
                return ".empty"
            if len(items) == 1 and 0 in items:
                return f"(.leaf {hex(items[0])})"
            left, right = {}, {}
            for key, v in items.items():
                if key:
                    index, side = divmod(key-1, 2)
                    (left if side == 0 else right)[index] = v
            expr = f"(.node {hex(items.get(0,0))} {render(left)} {render(right)})"
            if len(expr) > 5000:
                nodes += 1
                label = f"{name}Page{nodes}"
                self.add(f"def {label} : NTree := {expr}")
                return label
            return expr

        return render(items)


def geometry(directory):
    """Pack the twelve projections of each directed basis edge in lexicographic order."""
    directory = directory / "GeometryCache"
    directory.mkdir(parents=True, exist_ok=True)
    module = "CaccettaHaggkvist.GeometryCache."
    ns = "CaccettaHaggkvist.SixVertex.GeometryCache"
    slots = [tuple(range(k)) for k in (6, 5, 4, 3, 2)]
    slots += [(3,4,5), (0,1,4,5), (0,1,2,3,5), (0,3,4), (0,1,2,4), (0,1,3), (0,2,3,4,5)]
    unit = {}
    for a, b in itertools.product(range(6), repeat=2):
        frame = 0
        for s, coords in enumerate(slots):
            word = 0
            for j, v in enumerate(coords):
                digits = sum(((a == u and b == v) + 2*(a == v and b == u)) * 3**i
                             for i, u in enumerate(coords[:j]))
                word = word * 3**j + digits
            frame |= word << (32*s)
        unit[a,b] = frame
    orders = [tuple(p.index(v) for v in range(6)) for p in itertools.permutations(range(6))]
    bank = {}
    for a,b in unit:
        for start in range(0,720,16):
            data = sum(unit[q[a],q[b]] << (384*i) for i,q in enumerate(orders[start:start+16]))
            if data:
                bank[(6*a+b)*45 + start//16] = data
    src = Source(directory/"Data.lean", ns, ["CaccettaHaggkvist.SixVertexGeometry"])
    src.add(f"def bank : NTree := {src.tree('bank', bank)}")
    src.finish()
    edges = []
    for a,b in unit:
        label = f"Edge{a}{b}"
        edges.append(label)
        src = Source(directory/(label+".lean"), ns, [module+"Data"])
        src.add(f"set_option maxHeartbeats 0 in\nset_option maxRecDepth 32768 in\n"
                f"set_option exponentiation.threshold 512 in\n"
                f"theorem edge{a}{b} : Geometry.checkBankEdge bank {a} {b} = true := by decide +kernel")
        src.finish()
    src = Source(directory/"Valid.lean", ns, [module+label for label in edges])
    proof = ["theorem bank_valid (i j : Fin 6) : Geometry.checkBankEdge bank i j = true := by",
             "  fin_cases i <;> fin_cases j"]
    proof.extend(f"  · exact edge{a}{b}" for a,b in unit)
    src.add("\n".join(proof))
    src.finish()


class Compiler:
    def __init__(self, directory, name):
        self.dir = directory / name
        self.dir.mkdir(parents=True, exist_ok=True)
        self.lean = f"CaccettaHaggkvist.{name}"
        self.ns = f"CaccettaHaggkvist.SixVertex.{name}"
        self.blocks = []
        self.terms = []
        self.groups = defaultdict(list)

    def source(self, name, imports, sub=None):
        ns = self.ns if sub is None else self.ns + "." + sub
        return Source(self.dir / (name+".lean"), ns, imports)

    def gram(self, family, factors, scale, local, e):
        if not factors:
            return
        k, _, size, _, flags = family
        nf = len(flags)
        require(k + 2*(size-k) + e == 6, "Gram block uses the wrong number of coordinates")
        label = f"Block{len(self.blocks):02d}"
        self.blocks.append(label)
        src = self.source(label, ["CaccettaHaggkvist.SixVertexProgram", "CaccettaHaggkvist.SixVertexTables"], label)
        labels = labeled_entries(family, range(1, nf+1))
        src.table("labels", labels)
        divisor = 3**(math.comb(size,2)-math.comb(k,2))
        roots = {code//divisor for code in labels}
        require(len(roots) == 1, "Gram flags have inconsistent ordered roots")
        self.groups[k,size-k,e,local].append((label, roots.pop()))
        src.table("weights", {j: integer(f["w"]) for j, f in enumerate(factors)})
        src.table("coordinates", {j*nf+i: integer(x) for j,f in enumerate(factors)
                                  for i,x in enumerate(f["u"])}, signed=True)
        q = gram_matrix(factors, nf)
        src.table("entries", {i*(i+1)//2+j:q[i][j] for i in range(nf) for j in range(i+1)}, signed=True)
        src.add(f'''def gramBlock : CertificateGram where
  dim := {nf}
  rank := {len(factors)}
  flagId := fun word =>
    let id := labels.get word
    cond (Nat.beq id 0) {nf} (Nat.sub id 1)
  weight := fun t => Nat.mul {scale} (weights.get t)
  entry := fun i j => Int.mul {scale} (entries.signed (triangleIndex i j))
  factor := fun t i => coordinates.signed (Nat.add (Nat.mul t {nf}) i)''')
        src.add(f"def term : Term 6 := .gram {k} {size-k} {e} ({local}) gramBlock")
        src.finish()
        check = self.source(label+"Check", [self.lean+"."+label, "CaccettaHaggkvist.GramPacking"], label)
        fmax = max(abs(integer(x)) for f in factors for x in f["u"])
        qmax = scale * max(abs(x) for row in q for x in row)
        weight_sum = scale * sum(integer(f["w"]) for f in factors)
        bits = max(1, (qmax + weight_sum*fmax**2).bit_length())
        packed = {t:sum(integer(x) << (bits*j) for j,x in enumerate(f["u"])) for t,f in enumerate(factors)}
        check.table("polynomials", packed, signed=True)
        check.add(f"def packing : CertificateGram.Packing := ⟨{1 << bits},{fmax},{qmax},polynomials.signed⟩")
        check.add("set_option maxHeartbeats 0 in\nset_option maxRecDepth 32768 in\n"
                  "private theorem checkRows : packing.check gramBlock = true := Eq.refl true\n\n"
                  "theorem checked : term.check = true := packing.sound gramBlock checkRows")
        check.finish()
        self.terms.append(label+".term")

    def compile(self, cert, metadata, shard_size):
        require(cert["m"] == 6 and cert["num_models"] == 6583, "expected six-vertex certificate")
        alpha = Fraction(integer(cert["alpha_num"]), integer(cert["alpha_den"]))
        require(alpha >= Fraction(1037,1250), "unsupported CSS coefficient")
        rs = [Fraction(integer(a),integer(b)) for a,b in cert["r_fracs"]]
        ws = [Fraction(integer(a),integer(b)) for a,b in cert["r_sos_fracs"]]
        require(all(r >= 0 for r in rs+ws), "negative tangent")
        # Each CSS instruction is multiplied internally by q * rd².
        scale = alpha.denominator*math.lcm(1, *(r.denominator**2 for r in rs+ws))
        def local(kind, k, r):
            if kind == "ind":
                return f".inductionTerm ⟨{k}, by decide⟩ (by decide)", scale
            return (f".css ⟨{k}, by decide⟩ (by decide) {alpha.numerator} {alpha.denominator} "
                    f"{r.numerator} {r.denominator} (by decide) (by decide) (by decide)",
                    scale//(alpha.denominator*r.denominator**2))
        degree, base, ind, css, sos_ind, sos_css = metadata
        linear = self.source("Linear", ["CaccettaHaggkvist.SixVertexProgram","CaccettaHaggkvist.SixVertexTables"])
        linear.table("degreeWeight", labeled_entries((1,1,5,0,degree), [scale*integer(x) for x in cert["lam_int"]]), signed=True)
        self.terms.append("(.degree 4 degreeWeight.signed)")
        require(len(cert["sos_base"]) == len(base), "base block count mismatch")
        for fam, factors in zip(base, cert["sos_base"]):
            self.gram(fam, factors, scale, ".one", 0)

        mu = [0] * integer(cert["mu_len"])
        for i,v in cert["mu_sparse"]:
            i,v=integer(i),integer(v)
            require(0 <= i < len(mu) and not mu[i] and v>0,"invalid root multiplier")
            mu[i]=v
        tables = {}
        offset = 0
        for kind,active,fams,tangents in (("ind",cert["use_ind"],ind,[None]),("css",cert["use_css"],css,rs)):
            if active:
                for fam in fams:
                    for r in tangents:
                        nf = len(fam[-1])
                        part = mu[offset:offset+nf]
                        offset += nf
                        if not any(part):
                            continue
                        origin = fam[1]
                        descriptor,multiplier = local(kind,origin,r)
                        table = tables.setdefault((fam[2],descriptor),defaultdict(int))
                        for word,value in labeled_entries(fam,part).items():
                            table[word] += multiplier*value
        require(offset == len(mu),"unused or missing linear multipliers")
        for i,((k,descriptor),table) in enumerate(tables.items()):
            label = f"rootWeight{i}"
            linear.table(label,table)
            self.terms.append(f"(.linear (k := {k}) ({descriptor}) ⟨{max(table.values())}, {label}.get⟩)")
        linear.finish()
        extra = []
        if cert["use_sos_ind"]:
            extra.extend((f,1,"ind",None) for f in sos_ind)
        if cert["use_sos_css"]:
            extra.extend((f,2,"css",r) for f in sos_css for r in ws)
        require(len(extra)==len(cert["sos_ext"]),"weighted block count mismatch")
        for (fam,e,kind,r),factors in zip(extra,cert["sos_ext"]):
            descriptor,multiplier=local(kind,fam[1],r)
            self.gram(fam,factors,multiplier,descriptor,e)

        endpoints = [integer(cert[k]) for k in ("c_low_num","c_low_den","c_high_num","c_high_den")]
        ln,ld,hn,hd=endpoints
        require(0 < Fraction(ln,ld) <= Fraction(hn,hd) <= 1 and ld>0 and hd>0,"invalid interval")
        src=self.source("Data",["CaccettaHaggkvist.SixVertexReflection",self.lean+".Linear",
                                *(self.lean+"."+b for b in self.blocks)])
        src.add("def program : Program := [\n  "+",\n  ".join(self.terms)+"\n]")
        src.add(f"def endpoints : Endpoints := ⟨{ln},{ld},{hn},{hd}⟩")
        src.finish()
        valid=self.source("Valid", [self.lean+".Data",*(self.lean+"."+b+"Check" for b in self.blocks)])
        rewrites = ", ".join(b+".checked" for b in self.blocks)
        if rewrites:
            valid.add("theorem checked : program.check = true := by\n"
                      "  simp only [program, Program.check, List.all_cons, List.all_nil]\n"
                      f"  rw [{rewrites}]\n  rfl")
        else:
            valid.add("theorem checked : program.check = true := rfl")
        valid.finish()
        grouped = self.source("GroupedData", [self.lean+".Data","CaccettaHaggkvist.SixVertexGroups"])
        block_terms = {b+".term" for b in self.blocks}
        pieces = [".single "+t for t in self.terms if t not in block_terms]
        block_groups = []
        single_blocks = []
        for (k,d,e,descriptor), group in self.groups.items():
            if len(group) == 1 or len({root for _,root in group}) != len(group):
                pieces.extend(".single "+b+".term" for b,_ in group)
                single_blocks.extend(b for b,_ in group)
                continue
            name = "group"+str(len(block_groups))
            block_groups.append(name)
            divisor = 3**(math.comb(k+d,2)-math.comb(k,2))
            grouped.table(name+"Labels", {root:i+1 for i,(_,root) in enumerate(group)})
            grams = ", ".join(b+".gramBlock" for b,_ in group)
            grouped.add(f"def {name} : BlockGroup := ⟨[{grams}], fun code =>\n"
                        f"  let i := {name}Labels.get (Nat.div code {divisor})\n"
                        f"  cond (Nat.beq i 0) {len(group)} (Nat.sub i 1)⟩")
            pieces.append(f".grouped {k} {d} {e} ({descriptor}) {name}")
        grouped.add("def pieces : List (Piece 6) := [\n  "+",\n  ".join(pieces)+"\n]")
        grouped.finish()
        valid = self.source("GroupedValid", [self.lean+".GroupedData",self.lean+".Valid"])
        proof = ["theorem grouped_checked : (assemble pieces).check = true := by", "  apply assemble_checked"]
        proof.extend(f"  have h{b} : {b}.gramBlock.check = true := {b}.checked" for b in self.blocks)
        expansions = ["pieces", "Piece.check", *block_groups, *(b+".term" for b in single_blocks),
                      "Term.check", "List.all_cons", "List.all_nil", *("h"+b for b in self.blocks), "Bool.true_and"]
        proof.append("  simp only ["+", ".join(expansions)+"]")
        valid.add("\n".join(proof))
        valid.finish()
        checks = self.source("ModelCheck", [self.lean+".GroupedData","CaccettaHaggkvist.GeometryCache.Data"])
        checks.add("def acceptsModel (i : ℕ) : Bool :=\n"
                   "  endpoints.accepts (Geometry.packedRow GeometryCache.bank pieces (models6Tree.get i))")
        checks.finish()
        groups=[]
        for start in range(0,6583,shard_size):
            length=min(shard_size,6583-start)
            name=f"Rows{start:04d}"
            groups.append((name,start,length))
            src=self.source(name,[self.lean+".ModelCheck"])
            src.add("set_option maxHeartbeats 0\nset_option maxRecDepth 65536")
            for i in range(start,start+length):
                src.add(f"private theorem row{i} : acceptsModel {i} = true := by decide +kernel")
            proof = [f"theorem checkedRows{start} (i : ℕ) (lo : {start} ≤ i) (hi : i < {start+length}) :",
                     "    acceptsModel i = true := by", "  interval_cases i"]
            proof.extend(f"  · exact row{i}" for i in range(start,start+length))
            src.add("\n".join(proof))
            src.finish()
        bridge = self.source("Bridge", ["CaccettaHaggkvist.SixVertexBound",self.lean+".ModelCheck",
                                        self.lean+".GroupedValid","CaccettaHaggkvist.GeometryCache.Valid"])
        bridge.add(f"theorem bound_of_rows (hi : cStar ≤ ({hn} : ℝ) / {hd})\n"
                   f"    (rows : ∀ i : Fin 6583, acceptsModel i.val = true) : cStar ≤ ({ln} : ℝ) / {ld} := by\n"
                   "  apply cStar_le_of_program (assemble pieces) endpoints permutationTable_checked "
                   "grouped_checked (by decide) (by decide) hi\n"
                   "  intro i\n  rw [← Geometry.packedRow_eq GeometryCache.bank_valid]\n  exact rows i")
        bridge.finish()
        src=self.source("Result",[self.lean+".Bridge",
                                  *(self.lean+"."+name for name,_,_ in groups)])
        src.add("private def Window (a b : ℕ) : Prop := ∀ i, a ≤ i → i < b → acceptsModel i = true")
        src.add("private theorem joinWindows {a b c : ℕ} (l : Window a b) (r : Window b c) :\n"
                "    Window a c := by\n  intro i hl hh\n  by_cases h : i < b\n"
                "  · exact l i hl h\n  · exact r i (by omega) hh")
        def cover(parts):
            if len(parts) == 1:
                return f"checkedRows{parts[0][1]}"
            mid = len(parts)//2
            left, right = cover(parts[:mid]), cover(parts[mid:])
            lo = parts[0][1]
            hi = parts[-1][1] + parts[-1][2]
            label = f"window{lo}_{hi}"
            src.add(f"private theorem {label} : Window {lo} {hi} := joinWindows {left} {right}")
            return label
        all_rows = cover(groups)
        src.add(f"theorem bound (hi : cStar ≤ ({hn} : ℝ) / {hd}) : cStar ≤ ({ln} : ℝ) / {ld} :=\n"
                f"  bound_of_rows hi (fun i => {all_rows} i.val (Nat.zero_le _) i.isLt)")
        if Fraction(hn,hd)==Fraction(427,1250):
            src.add(f"theorem cStar_bound : cStar ≤ ({ln} : ℝ) / {ld} := bound (le_trans cStar_le_427_1250 (by norm_num))")
        src.finish()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("certificate",type=Path)
    p.add_argument("flags",type=Path)
    p.add_argument("extensions",type=Path)
    p.add_argument("lean_module_dir",type=Path,help="CaccettaHaggkvist module directory")
    p.add_argument("name",help="Lean namespace for this certificate")
    p.add_argument("--shard-size",type=int,default=12)
    a=p.parse_args()
    require(re.fullmatch("[A-Za-z][A-Za-z0-9_]*",a.name) is not None,"invalid Lean namespace")
    require(1 <= a.shard_size <= 6583,"invalid shard size")
    geometry(a.lean_module_dir)
    compiler=Compiler(a.lean_module_dir,a.name)
    compiler.compile(json.loads(a.certificate.read_bytes()),flag_ids(a.flags,a.extensions),a.shard_size)
    print(f"Generated {len(compiler.blocks)} Gram blocks and {len(compiler.terms)} instructions in {compiler.dir}")


if __name__=="__main__":
    main()
