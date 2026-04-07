# N-Queens(8) benchmark
def safe(col, queens, row):
    for i in range(len(queens)):
        qcol = queens[i]
        if col == qcol:
            return False
        if abs(col - qcol) == abs(row - (row - len(queens) + i)):
            return False
    return True

def nqueens(n, row, queens):
    if row == n:
        return 1
    count = 0
    for col in range(n):
        if safe(col, queens, row):
            count += nqueens(n, row + 1, queens + [col])
    return count

print(nqueens(8, 0, []))
