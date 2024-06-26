from ..helpers.polynomials import *
from ..helpers.linear_algebra import find_random_solution_linear_system, random_vector
from sage.structure.sequence import Sequence
from sage.matrix.constructor import matrix
from sage.matrix.special import identity_matrix, block_matrix
from math import floor, log2
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing


def replace_column(S, j, vec):
    """Replace the i-th column of S with the vector 'vector'"""
    m, n = S.dimensions()
    Fq = S.base_ring()
    S_copy = copy(S)
    for i in range(m):
        S_copy[i, j] = vec[i]
    return S_copy


def get_columns(S):
    m, n = S.dimensions()
    return [S.column(i) for i in range(n)]


def eq_coefficient(S, i, j, k, Seq):
    """Retuns the equation correspoing to the coefficient x_ij in the k-th poly in Seq"""
    f = Seq[k]
    S_columns = get_columns(S)
    vec_ij = vector(S_columns[i].outer_product(S_columns[j]))
    if i != j:
        vec_ji = vector(S_columns[j].outer_product(S_columns[i]))
        return (vec_ij + vec_ji) * vector(poly_to_poly_mat(f))
    else:
        return vec_ij * vector(poly_to_poly_mat(f))


def get_matrix_linear_system(eqs, var_vec):
    nrows = len(eqs)
    n = len(var_vec)
    Fq = eqs[0].base_ring()
    Mat = matrix(Fq, nrows, n)
    for i in range(nrows):
        f = eqs[i]
        for j in range(n):
            var = var_vec[j]
            coef_ij = f.coefficient(var)
            Mat[i, j] = coef_ij
    return Mat


def get_coefficient_matrix_with_vars(seq, variables):
    lure_poly = sum(variables)
    append_sec = seq + [lure_poly]
    C_lure, vec = Sequence(append_sec).coefficients_monomials()
    C = C_lure[0:-1, :]
    return C, vec


#################### Functions to test ###########################


def test_step2_polys_in_correct_shape(Seq_tw_after_substitution):
    m = len(Seq_tw_after_substitution)
    R = Seq_tw_after_substitution[0].parent()
    n = R.ngens()
    a = floor(n / m) - 1
    expected_monomials = set([R.gen(i) * R.gen(i) for i in range(m)] + [1])
    # expected_monomials.union(1)
    for k in range(a):
        f = Seq_tw_after_substitution[k]
        f_mon = set(f.monomials())
        if not f_mon.issubset(expected_monomials):
            print("Expected mon ", expected_monomials)
            print("Found mon ", f_mon)
            print(f"After step 2: {k}-th poly not in correct shape")
            return 0

    return 1


def is_thomae_wolf_poly(f, m):
    R = f.parent()
    for i in range(m):
        for j in range(i):
            if f.coefficient(R.gen(i) * R.gen(j)) != 0:
                return False
    return True


def is_thomae_wolf(sequence):
    m = len(sequence)
    f = sequence[0]
    n = f.parent().ngens()
    a = floor(n / m) - 1
    count = 0
    for f in sequence[:a]:
        if is_thomae_wolf_poly(f, m) == False:
            print(f"{count}-th polynomial doesn't have the correct share after Step 1")
            return False
        count += 1
    return True


####################  End functions to test ###########################


def replace_column_of_S0(n, m, col_idx, S, vec):
    """
    Input:
        - A matrix S of the form  ([[I_m, 0], [S0, I_n_minus_m]]), where S0 is a matrix of dimensions (n - m)  x m.
        - A vector over Fq of length n - m
        - An integer col_idx indicating the column of S0 to be replaced.

    Output: The matrix S with the col_idx-th column of S0 being replaced by vec

    """
    new_S = matrix(S.base_ring(), S.nrows(), S.ncols())

    # Copy the data from M to M_new
    for i in range(S.nrows()):
        for j in range(S.ncols()):
            new_S[i, j] = S[i, j]

    for i in range(n - m):
        new_S[m + i, col_idx] = vec[i]
    return new_S


def find_and_replace_column_of_S(n, m, a, col_idx, S, Matrices_A):
    """
    Input:
    - `a` number of matrices to be use from Matrices_A. While calling the function `a` must be n/m - 1.
    Solve the linear system requiered to find the col_id-th columns of S, that is, the col_id-th of S0,
    where S = ([[I_m, 0], [S0, I_n_minus_m]])

    Returns S with the col_id-th column of S0 replaced by the found vector.

    Note: this function assumes that the i-th of S0 inside S for i < col_idx is been already found.
    """
    if col_idx == 0:
        Fq = Matrices_A[0].base_ring()
        vec_sol = random_vector(Fq, n - m)
        new_S = replace_column_of_S0(n, m, col_idx, S, vec_sol)
    else:
        Eqs = []
        for mat in Matrices_A[:a]:
            for j in range(col_idx):
                eq_mat_1 = S.columns()[j] * mat * S.columns()[col_idx]
                eq_mat_2 = S.columns()[col_idx] * mat * S.columns()[j]
                eq = eq_mat_1 + eq_mat_2
                Eqs.append(eq)
        # lure_poly =  sum of the entries of the col_idx-th column of S0 +  1 e.g., s16 + s17 + s18 + s19 + s20 + s21 + s22 + s23 + 1
        lure_poly = sum(S.columns()[col_idx])
        # now we create the coefficient matrix of Eqs.
        # We add the lure polynomial to guerantee that all the linear monomials appear in the coeeficient matrix
        Eqs_with_lure = Eqs + [lure_poly]
        Coef_matrix_lure, vec_mon = Sequence(Eqs_with_lure).coefficients_monomials()
        Coef_matrix = Coef_matrix_lure[
            0:-1, :
        ]  # We remove the last column since it correspond to the lure_poly
        # Now we solve the system of the s_i
        A = Coef_matrix[:, :-1].dense_matrix()  # Columns of NONcostant terms
        b = Coef_matrix[:, -1].dense_matrix()  # Column of costant term
        vec_sol = A.solve_right(-b)
        new_S = replace_column_of_S0(n, m, col_idx, S, vec_sol)
    return new_S


def extract_linear_polynomials_L(f, m):
    """
    Input:
            - A polynomial f in n variables x_1,..., x_n, where
            - Integers n and m with m <=n

            We can write

                f = Q(x_1, ..., x_m) + \sum_{1<= i <= m} x_i L_i(x_{m+1}, ..., x_n) + H( L(x_{m+1}, ..., x_n),

            and the L_1, ..., L_m are linear polynomials.
    Output:
            -
    """
    L = []
    R = f.parent()
    n = R.ngens()
    for i in range(m):
        l = f.monomial_coefficient(R.gen(i))
        for j in range(m, n):
            coef = f.monomial_coefficient(R.gen(i) * R.gen(j))
            l += coef * R.gen(j)
        L.append(l)
    return L


####################Main Functions #############


def TW_step1(Seq):
    """
    Finds S and makes the composition.

    Output: [f \circ S for f in Seq] and S.

    """
    m = len(Seq)
    R = Seq[0].parent()
    n = R.ngens()
    Fq = R.base_ring()
    assert n > m
    a = floor(n / m) - 1
    RS = PolynomialRing(Fq, "s", (n - m) * m)
    S0 = matrix(RS, m, n - m, RS.gens()).transpose()
    I_m = identity_matrix(Fq, m, m)
    I_n_m = identity_matrix(Fq, n - m, n - m)
    O_m_n_m = matrix(Fq, m, n - m)
    S = block_matrix([[I_m, O_m_n_m], [S0, I_n_m]])
    Matrices_A, Vectors_b, Contant_terms = seq_to_seq_mat(Seq)
    solution_vecs_columns_S0 = []
    solution_vecs_columns_S0.append(random_vector(Fq, n - m))
    # Find and replace the columns of S0 within S one by one
    for col_idx in range(0, m):
        S = find_and_replace_column_of_S(n, m, a, col_idx, S, Matrices_A)
    S = S.change_ring(Fq)
    # print(S)
    Matrices_AS_new, Vectors_bS_new = seq_mat_compose_with_S(Matrices_A, Vectors_b, S)
    polys = seq_mat_to_seq(Matrices_AS_new, Vectors_bS_new, Contant_terms, R)
    return polys, S


def TW_step2(Seq_tw):
    """
    Input: -A sequence of polynomials Seq_tw of m polynomials in n variables.

    If every polynomial if written as

            f_k = Q_k(x_1, ..., x_m) + \sum_{1<= i <= m} x_i L_{k,i}(x_{m+1}, ..., x_n) + H_k( L(x_{m+1}, ..., x_n).
    This step takes the find a solution (a_{m+1},..., a_n) of the system L_{k,i}(x_{m+1}, ..., x_n) = 0 for k=1,..., a and i=1,...,m

    Output: [f(x_1, ..., x_m,a_{m+1},..., a_n) for f in Seq_tw]

    """
    R = Seq_tw[0].parent()
    Fq = R.base_ring()
    n = R.ngens()
    m = len(Seq_tw)
    var_restricted = R.gens()[:m]
    R_restricted = Seq_tw[0].parent()
    # Create a new polynomial ring with the first k variables
    R_restricted = PolynomialRing(Fq, names=[str(var) for var in var_restricted])
    a = floor(n / m) - 1
    L = []
    for k in range(a):  # range(a):
        f = Seq_tw[k]
        L_f = extract_linear_polynomials_L(f, m)
        L.extend(L_f)
    var_s = [R.gen(j) for j in range(m, n)]
    Coef_matrix, vec_var = get_coefficient_matrix_with_vars(
        L, var_s + [1]
    )  # Coefficient matrix
    A = Coef_matrix[:, :-1].dense_matrix()  # Columns of NONcostant terms
    b = Coef_matrix[:, -1].dense_matrix()  # Column of costant term
    solution_vector_of_L_polys = find_random_solution_linear_system(
        A, -b
    )  # Solution of the system L_1 = L_2 = ....=L_* = 0
    if (
        solution_vector_of_L_polys is None
    ):  # No solution to the system  L_1 = L_2 = ....=L_* = 0 exists.
        return None, None
    solution_as_list = list(solution_vector_of_L_polys.transpose()[0])
    specialized_values = dict(zip(var_s, solution_as_list))
    Seq_tw_after_substitution = [
        f.substitute(specialized_values) for f in Seq_tw
    ]  # Substitute the polys in the found solution
    Seq_tw_after_substitution = [R_restricted(f) for f in Seq_tw_after_substitution]
    return Seq_tw_after_substitution, specialized_values


def TW_step3(Seq_tw_after_substitution, use_magma=False):
    R_restricted = Seq_tw_after_substitution[0].parent()
    Fq = R_restricted.base_ring()
    n = R_restricted.ngens()
    m = len(Seq_tw_after_substitution)
    a = floor(n / m) - 1
    iter_num = 0
    sol_found = False
    q = len(Fq)
    exponent = int(log2(q)) - 1
    power = 2**exponent
    # print("power", power)
    # Extract Linear polynomials
    linear_polys = []
    for k in range(a):
        f = Seq_tw_after_substitution[k]
        l = f.constant_coefficient() ** power
        for i in range(m):
            coef = f.monomial_coefficient(R_restricted.gen(i) ** 2)
            l += coef**power * R_restricted.gen(i)
        linear_polys.append(l)
        print(linear_polys)
    final_polys = linear_polys + Seq_tw_after_substitution[a:]
    assert len(final_polys) == m
    var_x = R_restricted.gens()
    I = R_restricted.ideal(
        final_polys + [R_restricted.gen(i) ** q - R_restricted.gen(i) for i in range(m)]
    )
    #    I == R_restricted.ideal()
    if use_magma:
        B = I.groebner_basis("magma", prot=False)
    else:
        B = I.groebner_basis()
    dim_I = R_restricted.ideal(B).dimension()
    #    V = R_restricted.ideal(B).variety()
    if dim_I == 0:
        V = R_restricted.ideal(B).variety()
        v_sol = V[0]
        # print("Internal sol", v_sol)
        # print("Internal evals",  [f.substitute(v_sol) for f in Seq_tw_after_substitution])
        return v_sol
        # print(f"Variety []")
    iter_num += 1
    return None


def tw_strategy(Seq, max_iter_num=3, test=False, verbose=True, use_magma=False):
    v_sol = None
    iter_ = 0
    while v_sol is None and iter_ < max_iter_num:
        if verbose:
            print("Step 1: Started")

        Seq_tw, S = TW_step1(Seq)

        if test:
            if is_thomae_wolf(Seq_tw) == False:
                return None

        if verbose:
            print("Step 1: Done")

        if verbose:
            print("Step 2: Started")

        Seq_tw_after_substitution, specialized_values = TW_step2(Seq_tw)

        if verbose:
            print("Step 2: Done")
        if Seq_tw_after_substitution is not None:
            if test:
                test_step2_polys_in_correct_shape(Seq_tw_after_substitution)

            if verbose:
                print("Step 3: Started")

            v_sol = TW_step3(Seq_tw_after_substitution, use_magma=use_magma)
            iter_ += 1
            if v_sol is None:
                print("Not solution found at Step 3")
            if verbose:
                print("Step 3: Done")
        else:
            if verbose:
                print("Step 2: Not solution found for the L_i = 0 system")

    # Reconstruct full solution
    if v_sol is not None:
        R = Seq_tw[0].parent()
        v_sol_original_ring = {R(k): v for k, v in v_sol.items()}
        specialized_values.update(v_sol_original_ring)
        # print([f.substitute(specialized_values) for f in Seq_tw])
        full_sol = [specialized_values[R.gen(i)] for i in range(R.ngens())]
        # print(specialized_values)
        # print(full_sol)
        if full_sol is not None:
            true_sol = list(S * vector(full_sol))
            # print(S * vector(full_sol))
            return true_sol

    if verbose:
        print("No solution found!")
    return None

