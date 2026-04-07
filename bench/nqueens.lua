-- N-Queens(8) benchmark
function safe(col, queens, row)
    for i = 1, #queens do
        local qcol = queens[i]
        if col == qcol then return false end
        if math.abs(col - qcol) == math.abs(row - (row - #queens + i - 1)) then return false end
    end
    return true
end

function nqueens(n, row, queens)
    if row == n then return 1 end
    local count = 0
    for col = 0, n - 1 do
        if safe(col, queens, row) then
            local q2 = {}
            for i = 1, #queens do q2[i] = queens[i] end
            q2[#q2 + 1] = col
            count = count + nqueens(n, row + 1, q2)
        end
    end
    return count
end

print(nqueens(8, 0, {}))
