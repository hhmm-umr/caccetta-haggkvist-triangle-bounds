"""Common input and Gram matrix operations for the independent integer verifiers."""


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value):
    if type(value) is int or isinstance(value, str):
        return int(value)
    raise ValueError(f"expected an integer certificate coefficient, got {value!r}")


def read_records(stream, count, width):
    require(count >= 0, "negative table length")
    size = count * width
    data = stream.read(size)
    require(len(data) == size, f"incomplete table in {stream.name}")
    return data


def gram_matrix(factors, dimension):
    """Construct the symmetric integer matrix sum w u uᵀ."""
    if not factors:
        return None
    matrix = [[0] * dimension for _ in range(dimension)]
    for factor in factors:
        weight = integer(factor["w"])
        vector = [integer(x) for x in factor["u"]]
        require(weight > 0, f"nonpositive SOS weight {weight}")
        require(len(vector) == dimension, "SOS vector dimension mismatch")
        entries = [(i, x) for i, x in enumerate(vector) if x]
        for pos, (i, x) in enumerate(entries):
            row = matrix[i]
            scaled = weight * x
            for j, y in entries[:pos + 1]:
                row[j] += scaled * y
    for i, row in enumerate(matrix):
        for j in range(i):
            matrix[j][i] = row[j]
    return matrix
