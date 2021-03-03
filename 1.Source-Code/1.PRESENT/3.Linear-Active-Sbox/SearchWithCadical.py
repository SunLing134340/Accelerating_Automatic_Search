import os
import time
import random

FullRound = 32

SearchRoundStart = 1
SearchRoundEnd = 32
InitialLowerBound = 0

GroupConstraintChoice = 1

# Parameters for choice 1
GroupNumForChoice1 = 1

LinearActiveSbox = list([])
for i in range(FullRound):
    LinearActiveSbox += [0]
            
def CountClausesInRoundFunction(Round, ActiveSbox, clause_num):
    count = clause_num
    # Nonzero input
    count += 1
    # Cluases for Sbox
    for r in range(Round):
        for i in range(16):
            for j in range(39):
                count += 1
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
    TotalSbox = 16 * Round
    count_var_num = 0
    time_start = time.time()
    # Declare variables
    xin = []
    w = []
    xout = []
    for i in range(Round):
        xin.append([])
        w.append([])
        xout.append([])
        for j in range(64):
            xin[i].append(0)
        for j in range(16):
            w[i].append(0)
        for j in range(64):
            xout[i].append(0)
    # Allocate variables
    for i in range(Round):
        for j in range(64):
            xin[i][j] = count_var_num
            count_var_num += 1
        for j in range(16):
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
    Main_Var_Num = 16 * Round
    CardinalityCons = ActiveSbox
    count_clause_num = CountClausesInSequentialEncoding(Main_Var_Num, CardinalityCons, count_clause_num)
    # Count the number of clauses for Matsui's strategy
    for matsui_count in range(0, MatsuiCount):
        StartingRound = MatsuiRoundIndex[matsui_count][0]
        EndingRound = MatsuiRoundIndex[matsui_count][1]
        LeftNode = 16 * StartingRound
        RightNode = 16 * EndingRound - 1
        PartialCardinalityCons = ActiveSbox - LinearActiveSbox[StartingRound] - LinearActiveSbox[Round - EndingRound]
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
    for r in range(Round):
        y = list([])
        P = [0, 16, 32, 48, 1, 17, 33, 49, 2, 18, 34, 50, 3, 19, 35, 51, 4, 20, 36, 52, 5, 21, 37, 53, 6, 22, 38, 54, 7, 23, 39, 55, 8, 24, 40, 56, 9, 25, 41, 57, 10, 26, 42, 58, 11, 27, 43, 59, 12, 28, 44, 60, 13, 29, 45, 61, 14, 30, 46, 62, 15, 31, 47, 63]
        SymbolicCNFConstraintForSbox = [ # Linear PRESENT (39)
            [1, 0, 1, 0, 9, 0, 0, 9, 9], [1, 1, 0, 0, 0, 0, 9, 9, 9], [1, 1, 1, 1, 0, 1, 0, 9, 9], [9, 0, 0, 9, 1, 0, 1, 1, 9], [0, 0, 0, 9, 9, 9, 9, 0, 1], [1, 0, 0, 1, 1, 1, 1, 9, 9], [0, 1, 1, 9, 9, 1, 9, 1, 9], [1, 0, 1, 1, 9, 0, 1, 9, 9], [1, 1, 0, 1, 1, 0, 9, 9, 9], [1, 0, 1, 9, 0, 0, 1, 1, 9], [1, 0, 1, 9, 1, 0, 0, 1, 9], [1, 1, 0, 9, 0, 0, 1, 1, 9], [1, 1, 0, 9, 1, 0, 0, 1, 9], [0, 0, 0, 9, 1, 9, 9, 0, 9], [9, 9, 9, 0, 0, 0, 0, 9, 1], [0, 0, 0, 9, 9, 0, 9, 1, 9], [0, 0, 0, 0, 9, 9, 9, 1, 9], [0, 0, 0, 9, 9, 9, 1, 0, 9], [0, 9, 9, 1, 0, 0, 0, 9, 9], [9, 9, 9, 9, 0, 0, 0, 0, 1], [1, 9, 9, 9, 9, 9, 9, 9, 0], [9, 1, 9, 9, 9, 9, 9, 9, 0], [9, 9, 1, 9, 9, 9, 9, 9, 0], [9, 9, 9, 9, 9, 1, 9, 9, 0], [1, 1, 1, 9, 1, 1, 1, 9, 9], [1, 0, 0, 9, 0, 1, 0, 9, 9], [9, 9, 9, 1, 1, 0, 1, 1, 9], [0, 9, 1, 1, 1, 1, 0, 9, 9], [9, 9, 9, 0, 1, 0, 1, 0, 9], [0, 1, 9, 1, 0, 1, 1, 9, 9], [9, 1, 1, 0, 1, 9, 1, 9, 9], [0, 1, 9, 9, 1, 1, 0, 1, 9], [0, 9, 1, 9, 0, 1, 1, 1, 9], [0, 1, 1, 0, 0, 9, 0, 9, 9], [0, 9, 0, 0, 1, 1, 0, 9, 9], [0, 0, 9, 9, 1, 1, 0, 0, 9], [0, 9, 0, 9, 0, 1, 1, 0, 9], [0, 0, 9, 0, 0, 1, 1, 9, 9], [0, 1, 1, 9, 9, 0, 9, 0, 9]]
        for i in range(64):
            y += [xout[r][P[i]]]
        for i in range(16):
            for j in range(39):
                X = list([])
                for k in range(4):
                    X += [xin[r][4*i+k]]
                for k in range(4):
                    X += [y[4*i+k]]
                X += [w[r][i]]
                clauseseq = ""
                for k in range(9):
                    if (SymbolicCNFConstraintForSbox[j][k] == 1):
                        clauseseq += "-" + str(X[k] + 1) + " "
                    if (SymbolicCNFConstraintForSbox[j][k] == 0):
                        clauseseq += str(X[k] + 1) + " "
                clauseseq += "0" + "\n"
                file.write(clauseseq)
    # Add constraints for the original sequential encoding
    Main_Vars = list([])
    for r in range(Round):
        for i in range(16):
            Main_Vars += [w[Round - 1 - r][i]]
    GenSequentialEncoding(Main_Vars, auxiliary_var_u, Main_Var_Num, CardinalityCons, file)
    # Add constraints for Matsui's strategy
    for matsui_count in range(0, MatsuiCount):
        StartingRound = MatsuiRoundIndex[matsui_count][0]
        EndingRound = MatsuiRoundIndex[matsui_count][1]
        LeftNode = 16 * StartingRound
        RightNode = 16 * EndingRound - 1
        PartialCardinalityCons = ActiveSbox - LinearActiveSbox[StartingRound] - LinearActiveSbox[Round - EndingRound]
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
    LinearActiveSbox[totalround] = CountSbox - 1
    time_end = time.time()
    file = open("RunTimeSummarise.out", "a")
    resultseq = "Round: " + str(totalround) + "; Active S-box: " + str(LinearActiveSbox[totalround]) + "; Runtime: " + str(time_end - time_start) + "\n"
    file.write(resultseq)
    file.close()
print(str(LinearActiveSbox))
TotalTimeEnd = time.time()
print("Total Runtime: " + str(TotalTimeEnd - TotalTimeStart))
file = open("RunTimeSummarise.out", "a")
resultseq = "Total Runtime: " + str(TotalTimeEnd - TotalTimeStart)
file.write(resultseq)
