from z3 import *

# Statement 1
lam1 = Int('lam1')
lam1_1 = Int('lam1_1')
lam1_2 = Int('lam1_2')

# Statement 2, pt 1
lam2 = Int('lam2')
lam2_1 = Int('lam2_1')
lam2_3 = Int('lam2_3')
lam2_4 = Int('lam2_4')
lam2_5 = Int('lam2_5')

# Statement 2, pt 2
lam3 = Int('lam3')
lam3_2 = Int('lam3_2')
lam3_3 = Int('lam3_3')
lam3_4 = Int('lam3_4')
lam3_5 = Int('lam3_5')

# Statement 3, pt 1
lam4 = Int('lam4')
lam4_1 = Int('lam4_1')
lam4_3 = Int('lam4_3')
lam4_4 = Int('lam4_4')

# Statement 4, pt 1
lam5 = Int('lam5')
lam5_2 = Int('lam5_2')
lam5_3 = Int('lam5_3')
lam5_4 = Int('lam5_4')

# Let the solver determine the As
a1 = Int('a1')
a2 = Int('a2')
a3 = Int('a3')
a4 = Int('a4')
a5 = Int('a5')
a6 = Int('a6')

# Use the As from the paper
#a1 = -1
#a2 = 0
#a3 = -1
#a4 = 0
#a5 = 1
#a6 = -1

# Optionally require that the As are between -1 and 1:
a_constraint = And(a1 >= -1, a1 <= 1,
                   a2 >= -1, a2 <= 1,
                   a3 >= -1, a3 <= 1,
                   a4 >= -1, a4 <= 1,
                   a5 >= -1, a5 <= 1,
                   a6 >= -1, a6 <= 1)

# Positive
s0 = And(lam1 > 0, lam2 > 0, lam3 > 0, lam4 > 0, lam5 > 0,
         lam1_1 >= 0, lam1_2 >= 0,
         lam2_1 >= 0, lam2_3 >= 0, lam2_4 >= 0, lam2_5 >= 0,
         lam3_2 >= 0, lam3_3 >= 0, lam3_4 >= 0, lam3_5 >= 0,
         lam4_1 >= 0, lam4_3 >= 0, lam4_4 >= 0,
         lam5_2 >= 0, lam5_3 >= 0, lam5_4 >= 0)

s1 = And((-a2 * lam1_1 - a5 * lam1_2 == 0), (50 * a1 * lam1_1 - a3 * lam1_1 - lam1_1 + 50 * a4 * lam1_2 - a6 * lam1_2 - lam1_2 == -lam1))
s2 = And((lam2_1 * a1 - lam2_3 - lam2_4 * a1 - lam2_5 * a4 == 0), (lam2_1 * a2 - lam2_4 * a1 - lam2_4 * a2 - lam2_5 * a4 - lam2_5 * a5 == 0), (lam2_1 * a3 - lam2_3 + lam2_4 * (-a2 - a3 - 1) + lam2_5 * (-a5 - a6 - 1) == -lam2))
s3 = And((lam3_2 * a4 - lam3_3 - lam3_4 * a1 - lam3_5 * a4 == 0), (lam3_2 * a5 - lam3_4 * a1 - lam3_4 * a2 - lam3_5 * a4 - lam3_5 * a5 == 0), (lam3_2 * a6 - lam3_3 + lam3_4 * (-a2 - a3 - 1) + lam3_5 * (-a5 - a6 - 1) == -lam3))
s4 = And((lam4_1 * a1 + lam4_3 == 0), (lam4_1 * a2 - lam4_4 == 0), (lam4_1 * a3 == -lam4))
s5 = And((lam5_2 * a4 + lam5_3 == 0), (lam5_2 * a5 - lam5_4 == 0), (lam5_2 * a6 == -lam5))

print(solve(And(s0, s1, s2, s3, s4, s5)))
