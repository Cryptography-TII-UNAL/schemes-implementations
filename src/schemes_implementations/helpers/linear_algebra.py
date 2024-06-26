
from sage.matrix.constructor import Matrix, matrix
from sage.modules.free_module_element import vector

def find_random_solution_linear_system(A, c):
    """
    Returns a random solution to the system A*x = c
    If not solution exists it returns None
    """
    Fq = A.base_ring()
    try:
        x_particular = A.solve_right(c)
    except:
        return None
    NullSpace = A.right_kernel()

    # Generate a random linear combination of the basis vectors of the null space
    random_kernel_element = Matrix(Fq, x_particular.nrows(), 1, NullSpace.random_element())
    # print(random_kernel_element)
    # print(x_particular)
    # return x_particular + random_kernel_element
    return x_particular


def get_matrix_linear_system(eqs, var_vec):
    """

    :param eqs: linear equations
    :param var_vec: variables in the equations eqs
    :return: Matrix representation of the linear equations
    """
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


def random_vector(Fq, n):
    return vector([Fq.random_element() for _ in range(n)])