

from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector

def polynomial_homo_sequence(q, n, m):
    """Samples a sequence of m quadractic homogenous polynomial"""
    Seq = []
    Fq = GF(q)
    R = PolynomialRing(Fq, 'x', n)
    Deg2 = R.monomials_of_degree(2)
    for _ in range(m):
        f = sum([Fq.random_element() * mon for mon in Deg2]) + Fq.random_element()
        Seq.append(f)
    return Seq


def polynomial_sequence(q, n, m):
    """Samples a sequence of m quadractic polynomials in F_q[x_1,..., x_n]"""
    Seq = []
    Fq = GF(q)
    R = PolynomialRing(Fq, 'x', n)
    Deg2 = R.monomials_of_degree(2)
    for _ in range(m):
        f = sum([Fq.random_element() * mon for mon in Deg2]) + sum([Fq.random_element() * R.gen(i) for i in range(n)])  + Fq.random_element()
        Seq.append(f)
    return Seq


def poly_mat_to_poly(Matrix_A, vector_b, c, R):
    """form matrix representation F to poly in the poly ring R"""
    f = c
    n = R.ngens()
    x_vec = vector(R.gen(i) for i in range(n))
    Fx = Matrix_A * x_vec
    f += x_vec.dot_product(Fx)
    f += sum([x_vec[i] * vector_b[i] for i in range(n)])
    return f


def poly_to_poly_mat(f):
    """Returns the matrix repesentation of f"""
    R = f.parent()
    Fq = R.base_ring()
    n = R.ngens()
    A_f = matrix(Fq, n, n)
    b_f = n * [0]
    for i in range(n):
        b_f[i] = f.coefficient(R.gen(i)).constant_coefficient()
        for j in range(i, n):
            coef = f.coefficient(R.gen(i) * R.gen(j))
            A_f.add_to_entry(i, j, coef)
    return A_f, vector(Fq, b_f), f.constant_coefficient()


def poly_mat_compose_with_S(A_f, b_f, S):
    """Returns the matrix representation of f \circ S """
    Ring_S = S.parent()
    A_fS = S.transpose() * A_f * S
    b_fS = b_f * S
    return A_fS, b_fS


def seq_mat_to_seq(Matrices_A, Vectors_b, Contant_terms, R):
    Seq = []
    for i in range(len(Matrices_A)):
        f = poly_mat_to_poly(Matrices_A[i], Vectors_b[i], Contant_terms[i], R)
        Seq.append(f)
    return Seq


def seq_to_seq_mat(sequence):
    Matrices_A = []
    Vectors_b = []
    Contant_terms = []
    for f in sequence:
        A, b, c = poly_to_poly_mat(f)
        Matrices_A.append(A)
        Vectors_b.append(b)
        Contant_terms.append(c)

    return Matrices_A, Vectors_b, Contant_terms


def seq_mat_compose_with_S(Matrices_A, Vectors_b, S):
    Matrices_AS = []
    Vectors_bS = []
    for i in range(len(Matrices_A)):
        A_fS, b_fS = poly_mat_compose_with_S(Matrices_A[i], Vectors_b[i], S)
        Matrices_AS.append(A_fS)
        Vectors_bS.append(b_fS)
    return Matrices_AS, Vectors_bS