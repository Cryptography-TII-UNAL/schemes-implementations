from schemes_implementations.TW.tw import tw_strategy
from schemes_implementations.helpers.polynomials import polynomial_sequence

q = 4
n = 20
m = 6
Seq = polynomial_sequence(q, n, m)
true_sol = tw_strategy(Seq, max_iter_num=10, test=False, verbose=True, use_magma=False)
if true_sol is not None:
    print([f(true_sol) for f in Seq])
