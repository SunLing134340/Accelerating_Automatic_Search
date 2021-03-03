import os
import time
import random

FullRound = 33

SearchRoundStart = 1
SearchRoundEnd = 9
InitialLowerBound = 0

GroupConstraintChoice = 1

# Parameters for choice 1
GroupNumForChoice1 = 1

DiffActiveSbox = list([])
for i in range(FullRound):
    DiffActiveSbox += [0]
    
NumOfConstraint = [34, 34, 34, 34, 34, 34, 34, 34]
    
def CountClausesInRoundFunction(Round, ActiveSbox, clause_num):
    count = clause_num
    # Nonzero input
    count += 1
    # Cluases for Round function
    for r in range(Round):
        for block in range(8):
            count += NumOfConstraint[block]
        for i in range (32):
            count += 4
            count += 2
    return count
    
def CountClausesInSequentialEncoding(main_var_num, cardinalitycons, clause_num):
    count = clause_num
    n = main_var_num
    k = cardinalitycons
    if (k > 0):
        count += 1
        for j in range(1, k):
            count += 1
        for i in range(1, n-1):
            count += 3
        for j in range(1, k):
            for i in range(1, n-1):
                count += 2
        count += 1
    if (k == 0):
        for i in range(n):
            count += 1
    return count
    
def GenSequentialEncoding(x, u, main_var_num, cardinalitycons, fout):
    n = main_var_num
    k = cardinalitycons
    if (k > 0):
        clauseseq = "-" + str(x[0]+1) + " " + str(u[0][0]+1) + " 0" + "\n"
        fout.write(clauseseq)
        for j in range(1, k):
            clauseseq = "-" + str(u[0][j]+1) + " 0" + "\n"
            fout.write(clauseseq)
        for i in range(1, n-1):
            clauseseq = "-" + str(x[i]+1) + " " + str(u[i][0]+1) + " 0" + "\n"
            fout.write(clauseseq)
            clauseseq = "-" + str(u[i-1][0]+1) + " " + str(u[i][0]+1) + " 0" + "\n"
            fout.write(clauseseq)
            clauseseq = "-" + str(x[i]+1) + " " + "-" + str(u[i-1][k-1]+1) + " 0" + "\n"
            fout.write(clauseseq)
        for j in range(1, k):
            for i in range(1, n-1):
                clauseseq = "-" + str(x[i]+1) + " " + "-" + str(u[i-1][j-1]+1) + " " + str(u[i][j]+1) + " 0" + "\n"
                fout.write(clauseseq)
                clauseseq = "-" + str(u[i-1][j]+1) + " " + str(u[i][j]+1) + " 0" + "\n"
                fout.write(clauseseq)
        clauseseq = "-" + str(x[n-1]+1) + " " + "-" + str(u[n-2][k-1]+1) + " 0" + "\n"
        fout.write(clauseseq)
    if (k == 0):
        for i in range(n):
            clauseseq = "-" + str(x[i]+1) + " 0" + "\n"
            fout.write(clauseseq)
            
def CountClausesForMatsuiStrategy(n, k, left, right, m, clausenum):
    count = clausenum
    if (m > 0):
        if ((left == 0) and (right < n-1)):
            for i in range(1, right + 1):
                count += 1
        if ((left > 0) and (right == n-1)):
            for i in range(0, k-m):
                count += 1
            for i in range(0, k-m+1):
                count += 1
        if ((left > 0) and (right < n-1)):
            for i in range(0, k-m):
                count += 1
    if (m == 0):
        for i in range(left, right + 1):
            count += 1
    return count
    
def GenMatsuiConstraint(x, u, n, k, left, right, m, fout):
    if (m > 0):
        if ((left == 0) and (right < n-1)):
            for i in range(1, right + 1):
                clauseseq = "-" + str(x[i] + 1) + " " + "-" + str(u[i-1][m-1] + 1) + " 0" + "\n"
                fout.write(clauseseq)
        if ((left > 0) and (right == n-1)):
            for i in range(0, k-m):
                clauseseq = str(u[left-1][i] + 1) + " " + "-" + str(u[right - 1][i+m] + 1) + " 0" + "\n"
                fout.write(clauseseq)
            for i in range(0, k-m+1):
                clauseseq = str(u[left-1][i] + 1) + " " + "-" + str(x[right] + 1) + " " + "-" + str(u[right - 1][i+m-1] + 1) + " 0" + "\n"
                fout.write(clauseseq)
        if ((left > 0) and (right < n-1)):
            for i in range(0, k-m):
                clauseseq = str(u[left-1][i] + 1) + " " + "-" + str(u[right][i+m] + 1) + " 0" + "\n"
                fout.write(clauseseq)
    if (m == 0):
        for i in range(left, right + 1):
            clauseseq = "-" + str(x[i] + 1) + " 0" + "\n"
            fout.write(clauseseq)
            
def Decision(Round, ActiveSbox, MatsuiRoundIndex, MatsuiCount, flag):
    TotalSbox = 8 * Round
    count_var_num = 0
    time_start = time.time()
    # Declare variables
    xin = []
    sout = []
    w = []
    xout = []
    for i in range(Round):
        xin.append([])
        sout.append([])
        w.append([])
        xout.append([])
        for j in range(64):
            xin[i].append(0)
        for j in range(32):
            sout[i].append(0)
        for j in range(8):
            w[i].append(0)
        for j in range(64):
            xout[i].append(0)
    # Allocate variables
    for i in range(Round):
        for j in range(64):
            xin[i][j] = count_var_num
            count_var_num += 1
        for j in range(32):
            sout[i][j] = count_var_num
            count_var_num += 1
        for j in range(8):
            w[i][j] = count_var_num
            count_var_num += 1
    for i in range(Round - 1):
        for j in range(64):
            xout[i][j] = xin[i + 1][j]
    for i in range(64):
        xout[Round - 1][i] = count_var_num
        count_var_num += 1
    auxiliary_var_u = []
    for i in range(TotalSbox - 1):
        auxiliary_var_u.append([])
        for j in range(ActiveSbox):
            auxiliary_var_u[i].append(count_var_num)
            count_var_num += 1
    # Count the number of clauses in the round function
    count_clause_num = 0
    count_clause_num = CountClausesInRoundFunction(Round, ActiveSbox, count_clause_num)
    # Count the number of clauses in the original sequential encoding
    Main_Var_Num = 8 * Round
    CardinalityCons = ActiveSbox
    count_clause_num = CountClausesInSequentialEncoding(Main_Var_Num, CardinalityCons, count_clause_num)
    # Count the number of clauses for Matsui's strategy
    for matsui_count in range(0, MatsuiCount):
        StartingRound = MatsuiRoundIndex[matsui_count][0]
        EndingRound = MatsuiRoundIndex[matsui_count][1]
        LeftNode = 8 * StartingRound
        RightNode = 8 * EndingRound - 1
        PartialCardinalityCons = ActiveSbox - DiffActiveSbox[StartingRound] - DiffActiveSbox[Round - EndingRound]
        count_clause_num = CountClausesForMatsuiStrategy(Main_Var_Num, CardinalityCons, LeftNode, RightNode, PartialCardinalityCons, count_clause_num)
    # Open file
    file = open("Problem-Round" + str(Round) + "-Active" + str(ActiveSbox) + ".cnf", "w")
    file.write("p cnf " + str(count_var_num) + " " + str(count_clause_num) + "\n")
    # Add constraints to claim nonzero input difference
    clauseseq = ""
    for i in range(64):
        clauseseq += str(xin[0][i] + 1) + " "
    clauseseq += "0" + "\n"
    file.write(clauseseq)
    # Add constraints for the round function
    SymbolicCNFConstraintForSbox = [# Differential LBlock
        [[0, 9, 0, 9, 1, 1, 9, 0, 9], [0, 1, 1, 9, 1, 0, 9, 0, 9], [1, 1, 0, 9, 0, 1, 1, 1, 9], [1, 1, 0, 9, 1, 0, 1, 1, 9], [0, 9, 0, 0, 9, 1, 1, 1, 9], [0, 1, 1, 0, 9, 0, 9, 1, 9], [0, 1, 0, 1, 9, 0, 9, 1, 9], [9, 0, 9, 9, 0, 1, 0, 9, 9], [1, 9, 0, 9, 1, 1, 0, 1, 9], [9, 9, 9, 9, 0, 0, 0, 0, 1], [9, 0, 9, 0, 1, 9, 0, 0, 9], [1, 1, 1, 9, 1, 1, 9, 1, 9], [0, 9, 1, 0, 9, 1, 1, 0, 9], [1, 9, 0, 9, 0, 0, 0, 9, 9], [1, 0, 9, 9, 1, 0, 0, 1, 9], [0, 0, 0, 9, 9, 9, 1, 0, 9], [1, 1, 1, 9, 0, 0, 9, 1, 9], [0, 9, 1, 1, 9, 1, 1, 1, 9], [0, 0, 1, 1, 9, 9, 9, 1, 9], [0, 0, 1, 0, 9, 9, 9, 0, 9], [9, 1, 9, 1, 0, 9, 1, 0, 9], [0, 9, 0, 9, 0, 0, 9, 0, 1], [9, 9, 9, 9, 9, 9, 9, 1, 0], [1, 0, 9, 1, 9, 9, 1, 0, 9], [1, 0, 1, 9, 9, 9, 1, 1, 9], [0, 1, 9, 9, 9, 0, 0, 9, 9], [9, 1, 9, 9, 9, 9, 9, 9, 0], [0, 0, 0, 0, 9, 9, 9, 9, 1], [9, 9, 9, 9, 9, 9, 1, 9, 0], [9, 9, 9, 1, 9, 9, 9, 9, 0], [9, 1, 9, 0, 1, 9, 1, 0, 9], [1, 9, 9, 9, 0, 9, 0, 0, 9], [0, 9, 9, 9, 1, 9, 0, 0, 9], [0, 0, 9, 9, 9, 1, 0, 9, 9]],
        [[0, 9, 0, 9, 1, 1, 0, 9, 9], [0, 1, 1, 9, 1, 0, 0, 9, 9], [1, 1, 0, 9, 0, 1, 1, 1, 9], [1, 1, 0, 9, 1, 0, 1, 1, 9], [0, 9, 0, 0, 9, 1, 1, 1, 9], [0, 1, 1, 0, 9, 0, 1, 9, 9], [0, 1, 0, 1, 9, 0, 1, 9, 9], [9, 0, 9, 9, 0, 1, 9, 0, 9], [1, 9, 0, 9, 1, 1, 1, 0, 9], [9, 9, 9, 9, 0, 0, 0, 0, 1], [9, 0, 9, 0, 1, 9, 0, 0, 9], [1, 1, 1, 9, 1, 1, 1, 9, 9], [1, 9, 0, 9, 0, 0, 9, 0, 9], [1, 0, 9, 9, 1, 0, 1, 0, 9], [0, 9, 1, 0, 9, 1, 0, 1, 9], [0, 0, 0, 9, 9, 9, 0, 1, 9], [1, 1, 1, 9, 0, 0, 1, 9, 9], [0, 9, 1, 1, 9, 1, 1, 1, 9], [0, 0, 1, 1, 9, 9, 1, 9, 9], [0, 0, 1, 0, 9, 9, 0, 9, 9], [9, 1, 9, 1, 0, 9, 0, 1, 9], [0, 9, 0, 9, 0, 0, 0, 9, 1], [9, 9, 9, 9, 9, 9, 1, 9, 0], [1, 0, 9, 1, 9, 9, 0, 1, 9], [1, 0, 1, 9, 9, 9, 1, 1, 9], [0, 1, 9, 9, 9, 0, 9, 0, 9], [9, 1, 9, 9, 9, 9, 9, 9, 0], [0, 0, 0, 0, 9, 9, 9, 9, 1], [9, 9, 9, 9, 9, 9, 9, 1, 0], [9, 9, 9, 1, 9, 9, 9, 9, 0], [9, 1, 9, 0, 1, 9, 0, 1, 9], [1, 9, 9, 9, 0, 9, 0, 0, 9], [0, 9, 9, 9, 1, 9, 0, 0, 9], [0, 0, 9, 9, 9, 1, 9, 0, 9]],
        [[0, 9, 0, 9, 9, 1, 0, 1, 9], [0, 1, 1, 9, 9, 1, 0, 0, 9], [0, 9, 0, 9, 9, 0, 0, 0, 1], [1, 1, 0, 9, 1, 0, 1, 1, 9], [0, 9, 0, 0, 1, 9, 1, 1, 9], [1, 1, 0, 9, 1, 1, 1, 0, 9], [9, 0, 9, 0, 0, 9, 0, 9, 1], [9, 9, 9, 1, 0, 0, 0, 0, 9], [0, 1, 1, 0, 9, 9, 1, 0, 9], [0, 1, 0, 1, 9, 9, 1, 0, 9], [1, 9, 0, 9, 0, 1, 1, 1, 9], [0, 9, 1, 0, 1, 9, 0, 1, 9], [9, 0, 9, 9, 0, 0, 9, 1, 9], [1, 1, 1, 9, 9, 1, 1, 1, 9], [1, 0, 9, 9, 0, 1, 1, 0, 9], [0, 0, 0, 9, 1, 9, 0, 9, 9], [9, 9, 9, 9, 9, 9, 1, 9, 0], [0, 9, 1, 1, 1, 9, 1, 1, 9], [0, 0, 1, 1, 9, 9, 1, 9, 9], [0, 0, 1, 0, 9, 9, 0, 9, 9], [1, 9, 0, 9, 0, 0, 9, 0, 9], [1, 1, 1, 9, 9, 0, 1, 0, 9], [9, 1, 9, 1, 1, 0, 0, 9, 9], [1, 0, 9, 1, 1, 9, 0, 9, 9], [1, 0, 1, 9, 1, 9, 1, 9, 9], [0, 0, 0, 0, 9, 9, 9, 9, 1], [9, 9, 9, 9, 1, 9, 9, 9, 0], [0, 1, 9, 9, 0, 9, 9, 0, 9], [9, 9, 9, 9, 9, 9, 9, 1, 0], [9, 9, 9, 9, 9, 1, 9, 9, 0], [9, 1, 9, 0, 1, 1, 0, 9, 9], [1, 9, 9, 9, 0, 0, 0, 9, 9], [0, 9, 9, 9, 0, 1, 0, 9, 9], [0, 0, 9, 9, 0, 9, 9, 1, 9]],
        [[0, 9, 0, 9, 1, 9, 1, 0, 9], [0, 1, 1, 9, 0, 9, 1, 0, 9], [1, 1, 0, 9, 1, 1, 0, 1, 9], [1, 1, 0, 9, 0, 1, 1, 1, 9], [0, 9, 0, 0, 1, 1, 9, 1, 9], [0, 1, 1, 0, 0, 9, 9, 1, 9], [0, 1, 0, 1, 0, 9, 9, 1, 9], [9, 0, 9, 9, 1, 0, 0, 9, 9], [1, 9, 0, 9, 1, 0, 1, 1, 9], [9, 9, 9, 9, 0, 0, 0, 0, 1], [9, 0, 9, 0, 9, 0, 1, 0, 9], [1, 1, 1, 9, 1, 9, 1, 1, 9], [0, 9, 1, 0, 1, 1, 9, 0, 9], [1, 9, 0, 9, 0, 0, 0, 9, 9], [1, 0, 9, 9, 0, 0, 1, 1, 9], [0, 0, 0, 9, 9, 1, 9, 0, 9], [1, 1, 1, 9, 0, 9, 0, 1, 9], [0, 9, 1, 1, 1, 1, 9, 1, 9], [0, 0, 1, 1, 9, 9, 9, 1, 9], [0, 0, 1, 0, 9, 9, 9, 0, 9], [9, 1, 9, 1, 9, 1, 0, 0, 9], [0, 9, 0, 9, 0, 9, 0, 0, 1], [9, 9, 9, 9, 9, 9, 9, 1, 0], [1, 0, 9, 1, 9, 1, 9, 0, 9], [1, 0, 1, 9, 9, 1, 9, 1, 9], [0, 1, 9, 9, 0, 0, 9, 9, 9], [9, 1, 9, 9, 9, 9, 9, 9, 0], [0, 0, 0, 0, 9, 9, 9, 9, 1], [9, 9, 9, 9, 9, 1, 9, 9, 0], [9, 9, 9, 1, 9, 9, 9, 9, 0], [9, 1, 9, 0, 9, 1, 1, 0, 9], [1, 9, 9, 9, 9, 0, 0, 0, 9], [0, 9, 9, 9, 9, 0, 1, 0, 9], [0, 0, 9, 9, 1, 0, 9, 9, 9]],
        [[0, 9, 0, 9, 9, 1, 1, 0, 9], [0, 1, 1, 9, 9, 1, 0, 0, 9], [1, 1, 0, 9, 1, 0, 1, 1, 9], [1, 1, 0, 9, 1, 1, 0, 1, 9], [0, 9, 0, 0, 1, 9, 1, 1, 9], [0, 1, 1, 0, 9, 9, 0, 1, 9], [0, 1, 0, 1, 9, 9, 0, 1, 9], [9, 0, 9, 9, 0, 0, 1, 9, 9], [1, 9, 0, 9, 0, 1, 1, 1, 9], [9, 9, 9, 9, 0, 0, 0, 0, 1], [9, 0, 9, 0, 0, 1, 9, 0, 9], [1, 1, 1, 9, 9, 1, 1, 1, 9], [0, 9, 1, 0, 1, 9, 1, 0, 9], [1, 9, 0, 9, 0, 0, 0, 9, 9], [1, 0, 9, 9, 0, 1, 0, 1, 9], [0, 0, 0, 9, 1, 9, 9, 0, 9], [1, 1, 1, 9, 9, 0, 0, 1, 9], [0, 0, 1, 1, 9, 9, 9, 1, 9], [0, 9, 1, 1, 1, 9, 1, 1, 9], [0, 0, 1, 0, 9, 9, 9, 0, 9], [9, 1, 9, 1, 1, 0, 9, 0, 9], [0, 9, 0, 9, 9, 0, 0, 0, 1], [9, 9, 9, 9, 9, 9, 9, 1, 0], [1, 0, 9, 1, 1, 9, 9, 0, 9], [1, 0, 1, 9, 1, 9, 9, 1, 9], [0, 1, 9, 9, 0, 9, 0, 9, 9], [9, 1, 9, 9, 9, 9, 9, 9, 0], [0, 0, 0, 0, 9, 9, 9, 9, 1], [9, 9, 9, 9, 1, 9, 9, 9, 0], [9, 9, 9, 1, 9, 9, 9, 9, 0], [9, 1, 9, 0, 1, 1, 9, 0, 9], [1, 9, 9, 9, 0, 0, 9, 0, 9], [0, 9, 9, 9, 0, 1, 9, 0, 9], [0, 0, 9, 9, 0, 9, 1, 9, 9]],
        [[0, 9, 0, 9, 1, 9, 1, 0, 9], [0, 1, 1, 9, 1, 9, 0, 0, 9], [1, 1, 0, 9, 0, 1, 1, 1, 9], [1, 1, 0, 9, 1, 1, 0, 1, 9], [0, 9, 0, 0, 9, 1, 1, 1, 9], [0, 1, 1, 0, 9, 9, 0, 1, 9], [0, 1, 0, 1, 9, 9, 0, 1, 9], [9, 0, 9, 9, 0, 0, 1, 9, 9], [1, 9, 0, 9, 1, 0, 1, 1, 9], [9, 9, 9, 9, 0, 0, 0, 0, 1], [9, 0, 9, 0, 1, 0, 9, 0, 9], [1, 1, 1, 9, 1, 9, 1, 1, 9], [0, 9, 1, 0, 9, 1, 1, 0, 9], [1, 9, 0, 9, 0, 0, 0, 9, 9], [1, 0, 9, 9, 1, 0, 0, 1, 9], [0, 0, 0, 9, 9, 1, 9, 0, 9], [1, 1, 1, 9, 0, 9, 0, 1, 9], [0, 0, 1, 1, 9, 9, 9, 1, 9], [0, 9, 1, 1, 9, 1, 1, 1, 9], [0, 0, 1, 0, 9, 9, 9, 0, 9], [9, 1, 9, 1, 0, 1, 9, 0, 9], [0, 9, 0, 9, 0, 9, 0, 0, 1], [9, 9, 9, 9, 9, 9, 9, 1, 0], [1, 0, 9, 1, 9, 1, 9, 0, 9], [1, 0, 1, 9, 9, 1, 9, 1, 9], [0, 1, 9, 9, 9, 0, 0, 9, 9], [9, 1, 9, 9, 9, 9, 9, 9, 0], [0, 0, 0, 0, 9, 9, 9, 9, 1], [9, 9, 9, 9, 9, 1, 9, 9, 0], [9, 9, 9, 1, 9, 9, 9, 9, 0], [9, 1, 9, 0, 1, 1, 9, 0, 9], [1, 9, 9, 9, 0, 0, 9, 0, 9], [0, 9, 9, 9, 1, 0, 9, 0, 9], [0, 0, 9, 9, 9, 0, 1, 9, 9]],
        [[0, 9, 0, 9, 1, 1, 0, 9, 9], [0, 1, 1, 9, 1, 0, 0, 9, 9], [1, 1, 0, 9, 0, 1, 1, 1, 9], [1, 1, 0, 9, 1, 0, 1, 1, 9], [0, 9, 0, 0, 9, 1, 1, 1, 9], [0, 1, 1, 0, 9, 0, 1, 9, 9], [0, 1, 0, 1, 9, 0, 1, 9, 9], [9, 0, 9, 9, 0, 1, 9, 0, 9], [1, 9, 0, 9, 1, 1, 1, 0, 9], [9, 9, 9, 9, 0, 0, 0, 0, 1], [9, 0, 9, 0, 1, 9, 0, 0, 9], [1, 1, 1, 9, 1, 1, 1, 9, 9], [1, 9, 0, 9, 0, 0, 9, 0, 9], [1, 0, 9, 9, 1, 0, 1, 0, 9], [0, 9, 1, 0, 9, 1, 0, 1, 9], [0, 0, 0, 9, 9, 9, 0, 1, 9], [1, 1, 1, 9, 0, 0, 1, 9, 9], [0, 9, 1, 1, 9, 1, 1, 1, 9], [0, 0, 1, 1, 9, 9, 1, 9, 9], [0, 0, 1, 0, 9, 9, 0, 9, 9], [9, 1, 9, 1, 0, 9, 0, 1, 9], [0, 9, 0, 9, 0, 0, 0, 9, 1], [9, 9, 9, 9, 9, 9, 1, 9, 0], [1, 0, 9, 1, 9, 9, 0, 1, 9], [1, 0, 1, 9, 9, 9, 1, 1, 9], [0, 1, 9, 9, 9, 0, 9, 0, 9], [9, 1, 9, 9, 9, 9, 9, 9, 0], [0, 0, 0, 0, 9, 9, 9, 9, 1], [9, 9, 9, 9, 9, 9, 9, 1, 0], [9, 9, 9, 1, 9, 9, 9, 9, 0], [9, 1, 9, 0, 1, 9, 0, 1, 9], [1, 9, 9, 9, 0, 9, 0, 0, 9], [0, 9, 9, 9, 1, 9, 0, 0, 9], [0, 0, 9, 9, 9, 1, 9, 0, 9]],
        [[0, 9, 0, 9, 1, 1, 0, 9, 9], [0, 1, 1, 9, 1, 0, 0, 9, 9], [1, 1, 0, 9, 0, 1, 1, 1, 9], [1, 1, 0, 9, 1, 0, 1, 1, 9], [0, 9, 0, 0, 9, 1, 1, 1, 9], [0, 1, 1, 0, 9, 0, 1, 9, 9], [0, 1, 0, 1, 9, 0, 1, 9, 9], [9, 0, 9, 9, 0, 1, 9, 0, 9], [1, 9, 0, 9, 1, 1, 1, 0, 9], [9, 9, 9, 9, 0, 0, 0, 0, 1], [9, 0, 9, 0, 1, 9, 0, 0, 9], [1, 1, 1, 9, 1, 1, 1, 9, 9], [1, 9, 0, 9, 0, 0, 9, 0, 9], [1, 0, 9, 9, 1, 0, 1, 0, 9], [0, 9, 1, 0, 9, 1, 0, 1, 9], [0, 0, 0, 9, 9, 9, 0, 1, 9], [1, 1, 1, 9, 0, 0, 1, 9, 9], [0, 9, 1, 1, 9, 1, 1, 1, 9], [0, 0, 1, 1, 9, 9, 1, 9, 9], [0, 0, 1, 0, 9, 9, 0, 9, 9], [9, 1, 9, 1, 0, 9, 0, 1, 9], [0, 9, 0, 9, 0, 0, 0, 9, 1], [9, 9, 9, 9, 9, 9, 1, 9, 0], [1, 0, 9, 1, 9, 9, 0, 1, 9], [1, 0, 1, 9, 9, 9, 1, 1, 9], [0, 1, 9, 9, 9, 0, 9, 0, 9], [9, 1, 9, 9, 9, 9, 9, 9, 0], [0, 0, 0, 0, 9, 9, 9, 9, 1], [9, 9, 9, 9, 9, 9, 9, 1, 0], [9, 9, 9, 1, 9, 9, 9, 9, 0], [9, 1, 9, 0, 1, 9, 0, 1, 9], [1, 9, 9, 9, 0, 9, 0, 0, 9], [0, 9, 9, 9, 1, 9, 0, 0, 9], [0, 0, 9, 9, 9, 1, 9, 0, 9]]]
    Pi = [1, 3, 0, 2, 5, 7, 4, 6]
    for r in range(Round):
        for block in range(8):
            X = list([])
            for i in range(4):
                X += [xin[r][4 * block + i]]
            for i in range(4):
                X += [sout[r][4 * block + i]]
            X += [w[r][block]]
            for i in range(NumOfConstraint[7 - block]):
                clauseseq = ""
                for k in range(9):
                    if (SymbolicCNFConstraintForSbox[7 - block][i][k] == 1):
                        clauseseq += "-" + str(X[k] + 1) + " "
                    if (SymbolicCNFConstraintForSbox[7 - block][i][k] == 0):
                        clauseseq += str(X[k] + 1) + " "
                clauseseq += "0" + "\n"
                file.write(clauseseq)
        XorInput1 = list([])
        for i in range(8):
            for j in range(4):
                XorInput1 += [sout[r][4 * Pi[i] + j]]
        XorInput2 = list([])
        for i in range(24):
            XorInput2 += [xin[r][32 + i + 8]]
        for i in range(24, 32):
            XorInput2 += [xin[r][32 + i - 24]]
        for i in range(32):
            a = XorInput1[i]
            b = XorInput2[i]
            c = xout[r][i]
            clauseseq = str(a + 1) + " " + str(b + 1) + " " + "-" + str(c + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            clauseseq = str(a + 1) + " " + "-" + str(b + 1) + " " + str(c + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            clauseseq = "-" + str(a + 1) + " " + str(b + 1) + " " + str(c + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            clauseseq = "-" + str(a + 1) + " " + "-" + str(b + 1) + " " + "-" + str(c + 1) + " " + "0" + "\n"
            file.write(clauseseq)
        for i in range(32):
            a = xin[r][i]
            b = xout[r][32 + i]
            clauseseq = str(a + 1) + " " + "-" + str(b + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            clauseseq = "-" + str(a + 1) + " " + str(b + 1) + " " + "0" + "\n"
            file.write(clauseseq)
    # Add constraints for the original sequential encoding
    Main_Vars = list([])
    for r in range(Round):
        for i in range(8):
            Main_Vars += [w[Round - 1 - r][i]]
    GenSequentialEncoding(Main_Vars, auxiliary_var_u, Main_Var_Num, CardinalityCons, file)
    # Add constraints for Matsui's strategy
    for matsui_count in range(0, MatsuiCount):
        StartingRound = MatsuiRoundIndex[matsui_count][0]
        EndingRound = MatsuiRoundIndex[matsui_count][1]
        LeftNode = 8 * StartingRound
        RightNode = 8 * EndingRound - 1
        PartialCardinalityCons = ActiveSbox - DiffActiveSbox[StartingRound] - DiffActiveSbox[Round - EndingRound]
        GenMatsuiConstraint(Main_Vars, auxiliary_var_u, Main_Var_Num, CardinalityCons, LeftNode, RightNode, PartialCardinalityCons, file)
    file.close()
    # Call solver cadical
    order = "~/Install/cadical/build/cadical " + "Problem-Round" + str(Round) + "-Active" + str(ActiveSbox) + ".cnf > Round" + str(Round) + "-Active" + str(ActiveSbox) + "-solution.out"
    os.system(order)
    # Extracting results
    order = "sed -n '/s SATISFIABLE/p' Round" + str(Round) + "-Active" + str(ActiveSbox) + "-solution.out > SatSolution.out"
    os.system(order)
    order = "sed -n '/s UNSATISFIABLE/p' Round" + str(Round) + "-Active" + str(ActiveSbox) + "-solution.out > UnsatSolution.out"
    os.system(order)
    satsol = open("SatSolution.out")
    unsatsol = open("UnsatSolution.out")
    satresult = satsol.readlines()
    unsatresult = unsatsol.readlines()
    satsol.close()
    unsatsol.close()
    if ((len(satresult) == 0) and (len(unsatresult) > 0)):
        flag = False
    if ((len(satresult) > 0) and (len(unsatresult) == 0)):
        flag = True
    order = "rm SatSolution.out"
    os.system(order)
    order = "rm UnsatSolution.out"
    os.system(order)
    # Removing cnf file
    order = "rm Problem-Round" + str(Round) + "-Active" + str(ActiveSbox) + ".cnf"
    os.system(order)
    time_end = time.time()
    # Printing solutions
    if (flag == True):
        print("Round:" + str(Round) + "; Active: " + str(ActiveSbox) + "; Sat; TotalCost: " + str(time_end - time_start))
    else:
        print("Round:" + str(Round) + "; Active: " + str(ActiveSbox) + "; Unsat; TotalCost: " + str(time_end - time_start))
    return flag
            
# main function
CountSbox = InitialLowerBound
TotalTimeStart = time.time()
for totalround in range(SearchRoundStart, SearchRoundEnd):
    flag = False
    time_start = time.time()
    MatsuiRoundIndex = []
    MatsuiCount = 0
    # Generate Matsui condition under choice 1
    if (GroupConstraintChoice == 1):
        for group in range(0, GroupNumForChoice1):
            for round in range(1, totalround - group + 1):
                MatsuiRoundIndex.append([])
                MatsuiRoundIndex[MatsuiCount].append(group)
                MatsuiRoundIndex[MatsuiCount].append(group + round)
                MatsuiCount += 1
    # Printing Matsui conditions
    file = open("MatsuiCondition.out", "a")
    resultseq = "Round: " + str(totalround) + "; Partial Constraint Num: " + str(MatsuiCount) + "\n"
    file.write(resultseq)
    file.write(str(MatsuiRoundIndex) + "\n")
    file.close()
    while (flag == False):
        flag = Decision(totalround, CountSbox, MatsuiRoundIndex, MatsuiCount, flag)
        CountSbox += 1
    DiffActiveSbox[totalround] = CountSbox - 1
    time_end = time.time()
    file = open("RunTimeSummarise.out", "a")
    resultseq = "Round: " + str(totalround) + "; Active S-box: " + str(DiffActiveSbox[totalround]) + "; Runtime: " + str(time_end - time_start) + "\n"
    file.write(resultseq)
    file.close()
print(str(DiffActiveSbox))
TotalTimeEnd = time.time()
print("Total Runtime: " + str(TotalTimeEnd - TotalTimeStart))
file = open("RunTimeSummarise.out", "a")
resultseq = "Total Runtime: " + str(TotalTimeEnd - TotalTimeStart)
file.write(resultseq)
