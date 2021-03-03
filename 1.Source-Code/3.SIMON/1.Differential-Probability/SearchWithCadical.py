import os
import time
import random

FullRound = 33

BlockSize = 32
HalfBlockSize = 16

SearchRoundStart = 1
SearchRoundEnd = 33
InitialLowerBound = 0

RotateA = 8
RotateB = 1
RotateC = 2
Rotate2AB = 2 * RotateA - RotateB
RotateAB = RotateA - RotateB

GroupConstraintChoice = 1

# Parameters for choice 1
GroupNumForChoice1 = 1

DifferentialProbabilityBound = list([])
for i in range(FullRound):
    DifferentialProbabilityBound += [0]
    
def CountClausesInRoundFunction(Round, Prob, clausenum):
    count = clausenum
    # Nonzero input
    count += 1
    for round in range(Round):
        for i in range(HalfBlockSize):
            count += 3
        for i in range(HalfBlockSize):
            count += 4
        for i in  range(HalfBlockSize):
            count += 2
        for i in range(HalfBlockSize):
            count += 1
        for i in range(HalfBlockSize):
            count += 2
        for i in range(HalfBlockSize):
            count += 8
        for i in range(HalfBlockSize):
            count += 4
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
            
def Decision(Round, Probability, MatsuiRoundIndex, MatsuiCount, flag):
    TotalProbability = HalfBlockSize * Round
    count_var_num = 0
    time_start = time.time()
    # Declare variable
    xin = []
    z = []
    varibits = []
    doublebits = []
    w = []
    xout = []
    for i in range(Round):
        xin.append([])
        z.append([])
        varibits.append([])
        doublebits.append([])
        w.append([])
        xout.append([])
        for j in range(BlockSize):
            xin[i].append(0)
        for j in range(HalfBlockSize):
            z[i].append(0)
            varibits[i].append(0)
            doublebits[i].append(0)
            w[i].append(0)
        for j in range(BlockSize):
            xout[i].append(0)
    # Allocate variable
    for i in range(Round):
        for j in range(BlockSize):
            xin[i][j] = count_var_num
            count_var_num += 1
        for j in range(HalfBlockSize):
            z[i][j] = count_var_num
            count_var_num += 1
        for j in range(HalfBlockSize):
            varibits[i][j] = count_var_num
            count_var_num += 1
        for j in range(HalfBlockSize):
            doublebits[i][j] = count_var_num
            count_var_num += 1
        for j in range(HalfBlockSize):
            w[i][j] = count_var_num
            count_var_num += 1
    for i in range(Round - 1):
        for j in range(BlockSize):
            xout[i][j] = xin[i + 1][j]
    for i in range(BlockSize):
        xout[Round - 1][i] = count_var_num
        count_var_num += 1
    auxiliary_var_u = []
    for i in range(TotalProbability - 1):
        auxiliary_var_u.append([])
        for j in range(Probability):
            auxiliary_var_u[i].append(count_var_num)
            count_var_num += 1
    # Count the number of clauses in the round function
    count_clause_num = 0
    count_clause_num = CountClausesInRoundFunction(Round, Probability, count_clause_num)
    # Count the number of clauses in the original sequential encoding
    Main_Var_Num = HalfBlockSize * Round
    CardinalityCons = Probability
    count_clause_num = CountClausesInSequentialEncoding(Main_Var_Num, CardinalityCons, count_clause_num)
    # Count the number of clauses for Matsui's strategy
    for matsui_count in range(0, MatsuiCount):
        StartingRound = MatsuiRoundIndex[matsui_count][0]
        EndingRound = MatsuiRoundIndex[matsui_count][1]
        LeftNode = HalfBlockSize * StartingRound
        RightNode = HalfBlockSize * EndingRound - 1
        PartialCardinalityCons = Probability - DifferentialProbabilityBound[StartingRound] - DifferentialProbabilityBound[Round - EndingRound]
        count_clause_num = CountClausesForMatsuiStrategy(Main_Var_Num, CardinalityCons, LeftNode, RightNode, PartialCardinalityCons, count_clause_num)
    # Open file
    file = open("Problem-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf", "w")
    file.write("p cnf " + str(count_var_num) + " " + str(count_clause_num) + "\n")
    # Add constraints to claim nonzero input difference
    clauseseq = ""
    for i in range(BlockSize):
        clauseseq += str(xin[0][i] + 1) + " "
    clauseseq += "0" + "\n"
    file.write(clauseseq)
    # Add constraints for the round function
    for round in range(Round):
        x_i = list([])
        y_i = list([])
        x_ip1 = list([])
        y_ip1 = list([])
        for i in range(HalfBlockSize):
            x_i += [xin[round][i]]
            y_i += [xin[round][i + HalfBlockSize]]
            x_ip1 += [xout[round][i]]
            y_ip1 += [xout[round][i + HalfBlockSize]]
        SA = list([])
        for i in range(HalfBlockSize - RotateA):
            SA += [x_i[i + RotateA]]
        for i in range(HalfBlockSize - RotateA, HalfBlockSize):
            SA += [x_i[i - (HalfBlockSize - RotateA)]]
        SB = list([])
        for i in range(HalfBlockSize - RotateB):
            SB += [x_i[i + RotateB]]
        for i in range(HalfBlockSize - RotateB, HalfBlockSize):
            SB += [x_i[i - (HalfBlockSize - RotateB)]]
        for i in range(HalfBlockSize):
            # The first clause
            clauseseq = "-" + str(SA[i] + 1) + " " + str(varibits[round][i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The second clause
            clauseseq = "-" + str(SB[i] + 1) + " " + str(varibits[round][i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The third clause
            clauseseq = str(SA[i] + 1) + " " + str(SB[i] + 1) + " -" + str(varibits[round][i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
        S2AB = list([])
        for i in range(HalfBlockSize - Rotate2AB):
            S2AB += [x_i[i + Rotate2AB]]
        for i in range(HalfBlockSize - Rotate2AB, HalfBlockSize):
            S2AB += [x_i[i - (HalfBlockSize - Rotate2AB)]]
        for i in range(HalfBlockSize):
            # The first clause
            clauseseq = str(SB[i] + 1) + " -" + str(doublebits[round][i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The second clause
            clauseseq = "-" + str(SB[i] + 1) + " " + str(S2AB[i] + 1) + " -" + str(doublebits[round][i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The third clause
            clauseseq = "-" + str(SB[i] + 1) + " -" + str(SA[i] + 1) + " -" + str(doublebits[round][i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The fourth clause
            clauseseq = "-" + str(SB[i] + 1) + " " + str(SA[i] + 1) + " -" + str(S2AB[i] + 1) + " " + str(doublebits[round][i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
        for i in range(HalfBlockSize):
            # The first clause
            clauseseq = str(y_ip1[i] + 1) + " -" + str(x_i[i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The second clause
            clauseseq = "-" + str(y_ip1[i] + 1) + " " + str(x_i[i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
        for i in range(HalfBlockSize):
            clauseseq = "-" + str(z[round][i] + 1) + " " + str(varibits[round][i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
        SAB = list([])
        for i in range(HalfBlockSize - RotateAB):
            SAB += [z[round][i + RotateAB]]
        for i in range(HalfBlockSize - RotateAB, HalfBlockSize):
            SAB += [z[round][i - (HalfBlockSize - RotateAB)]]
        for i in range(HalfBlockSize):
            # The first clause
            clauseseq = str(z[round][i] + 1) + " -" + str(SAB[i] + 1) + " -" + str(doublebits[round][i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The second clause
            clauseseq = "-" + str(z[round][i] + 1) + " " + str(SAB[i] + 1) + " -" + str(doublebits[round][i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
        SC = list([])
        for i in range(HalfBlockSize - RotateC):
            SC += [x_i[i + RotateC]]
        for i in range(HalfBlockSize - RotateC, HalfBlockSize):
            SC += [x_i[i - (HalfBlockSize - RotateC)]]
        for i in range(HalfBlockSize):
            # The first clause
            clauseseq = str(y_i[i] + 1) + " " + str(z[round][i] + 1) + " " + str(SC[i] + 1) + " -" + str(x_ip1[i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The second clause
            clauseseq = str(y_i[i] + 1) + " " + str(z[round][i] + 1) + " -" + str(SC[i] + 1) + " " + str(x_ip1[i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The third clause
            clauseseq = str(y_i[i] + 1) + " -" + str(z[round][i] + 1) + " " + str(SC[i] + 1) + " " + str(x_ip1[i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The fourth clause
            clauseseq = str(y_i[i] + 1) + " -" + str(z[round][i] + 1) + " -" + str(SC[i] + 1) + " -" + str(x_ip1[i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The fifth clause
            clauseseq = "-" + str(y_i[i] + 1) + " " + str(z[round][i] + 1) + " " + str(SC[i] + 1) + " " + str(x_ip1[i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The sixth clause
            clauseseq = "-" + str(y_i[i] + 1) + " " + str(z[round][i] + 1) + " -" + str(SC[i] + 1) + " -" + str(x_ip1[i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The seventh clause
            clauseseq = "-" + str(y_i[i] + 1) + " -" + str(z[round][i] + 1) + " " + str(SC[i] + 1) + " -" + str(x_ip1[i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The eighth clause
            clause = "-" + str(y_i[i] + 1) + " -" + str(z[round][i] + 1) + " -" + str(SC[i] + 1) + " " + str(x_ip1[i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
        for i in range(HalfBlockSize):
            # The first clause
            clauseseq = str(varibits[round][i] + 1) + " " + str(doublebits[round][i] + 1) + " -" + str(w[round][i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The second clause
            clauseseq = str(varibits[round][i] + 1) + " -" + str(doublebits[round][i] + 1) + " " + str(w[round][i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The third clause
            clauseseq = "-" + str(varibits[round][i] + 1) + " " + str(doublebits[round][i] + 1) + " " + str(w[round][i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            # The fourth clause
            clauseseq = "-" + str(varibits[round][i] + 1) + " -" + str(doublebits[round][i] + 1) + " -" + str(w[round][i] + 1) + " " + "0" + "\n"
            file.write(clauseseq)
    # Add constraints for the original sequential encoding
    Main_Vars = list([])
    for r in range(Round):
        for i in range(HalfBlockSize):
            Main_Vars += [w[Round - 1 - r][i]]
    GenSequentialEncoding(Main_Vars, auxiliary_var_u, Main_Var_Num, CardinalityCons, file)
    # Add constraints for Matsui's strategy
    for matsui_count in range(0, MatsuiCount):
        StartingRound = MatsuiRoundIndex[matsui_count][0]
        EndingRound = MatsuiRoundIndex[matsui_count][1]
        LeftNode = HalfBlockSize * StartingRound
        RightNode = HalfBlockSize * EndingRound - 1
        PartialCardinalityCons = Probability - DifferentialProbabilityBound[StartingRound] - DifferentialProbabilityBound[Round - EndingRound]
        GenMatsuiConstraint(Main_Vars, auxiliary_var_u, Main_Var_Num, CardinalityCons, LeftNode, RightNode, PartialCardinalityCons, file)
    file.close()
    # Call solver cadical
    order = "/dataspace/cadical/build/cadical " + "Problem-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf > Round" + str(Round) + "-Probability" + str(Probability) + "-solution.out"
    os.system(order)
    # Extracting results
    order = "sed -n '/s SATISFIABLE/p' Round" + str(Round) + "-Probability" + str(Probability) + "-solution.out > SatSolution.out"
    os.system(order)
    order = "sed -n '/s UNSATISFIABLE/p' Round" + str(Round) + "-Probability" + str(Probability) + "-solution.out > UnsatSolution.out"
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
    order = "rm Problem-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf"
    os.system(order)
    time_end = time.time()
    # Printing solutions
    if (flag == True):
        print("Round:" + str(Round) + "; Probability: " + str(Probability) + "; Sat; TotalCost: " + str(time_end - time_start))
    else:
        print("Round:" + str(Round) + "; Probability: " + str(Probability) + "; Unsat; TotalCost: " + str(time_end - time_start))
    return flag
            
# main function
CountProbability = InitialLowerBound
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
        flag = Decision(totalround, CountProbability, MatsuiRoundIndex, MatsuiCount, flag)
        CountProbability += 1
    DifferentialProbabilityBound[totalround] = CountProbability - 1
    CountProbability = CountProbability - 1
    time_end = time.time()
    file = open("RunTimeSummarise.out", "a")
    resultseq = "Round: " + str(totalround) + "; Differential Probability: " + str(DifferentialProbabilityBound[totalround]) + "; Runtime: " + str(time_end - time_start) + "\n"
    file.write(resultseq)
    file.close()
print(str(DifferentialProbabilityBound))
TotalTimeEnd = time.time()
print("Total Runtime: " + str(TotalTimeEnd - TotalTimeStart))
file = open("RunTimeSummarise.out", "a")
resultseq = "Total Runtime: " + str(TotalTimeEnd - TotalTimeStart)
file.write(resultseq)
