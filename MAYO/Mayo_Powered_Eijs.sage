#!/usr/bin/env python
# coding: utf-8

# # Mayo Signature Scheme (Powers of $E$)
# 
# __Remark:__ The current notebook works for $q>2$.
# 
# https://pqmayo.org/about/
# 
# https://eprint.iacr.org/2021/1144.pdf
# 
# ### Efficient Implementation
# 
# https://eprint.iacr.org/2023/1683.pdf

# In[1]:


# Functions needed to generate the Mayo keys

def Upper(M):
    """
    input:
    M = square matrix
    
    output:
    Upper triangular matrix that defines the same quadratic form as M
    """
    nn = M.ncols()
    #F_q = M.base_ring()
    #q = F_q.order()
    limit = 1
    for i in range(nn):
        for j in range(i+limit, nn):
            M[i, j] += M[j, i]
            M[j, i] = 0
    return M

def Eval(F, x):
    """
    input:
    F = list of square matrices of size len(x)
    x = a vector with entries in F_q
    
    output:
    vector with the evaluation at x of the quadratic forms defined by the matrices in F
    """
    return vector([ x*M*x for M in F])

def Get_UOV_Keys(n, m, o, q):
    """
    input:
    n = number of variables
    m = number of polynomials
    o = dimension of the Oil space
    q = size of the field F_q
    
    output:
    F_q = field of size q
    P = list with block matrices of the UOV part
    Public_key = list with public key matrices of the UOV part
    Public_key_polar = list with the polar form public key matrices of the UOV part
    O = random matrix of order (n-o)xo
    O_bar = Oil space of the UOV map = [O | I_o]^T
    """
    # The dimension of the Oil space O is o
    F_q.<w> = GF(q)
    O = random_matrix(F_q, n-o, o)
    O_bar = block_matrix([[O], [identity_matrix(F_q,o)]])
    P = []
    Public_key = []
    Public_key_polar = []
    for i in range(0, m):
        P1 = Upper(random_matrix(F_q, n-o, n-o))
        P2 = random_matrix(F_q, n-o, o)
        P3 = Upper(-O.transpose()*P1*O-O.transpose()*P2)
        P.append([P1, P2, P3])
        matriz = block_matrix([[P1, P2], [zero_matrix(F_q, o, n-o), P3]])
        Public_key.append(matriz)
        Public_key_polar.append(matriz+matriz.transpose())
    return F_q, P, Public_key, Public_key_polar, O, O_bar

def Check_Oil(Public_key, O_bar):
    """
    input:
    Public_key = list with public key matrices of the UOV part
    O_bar = Oil space of the UOV map = [O | I_o]^T
    
    output:
    evaluation of the public key polynomials at every basis vector of O_bar
    to check that they all vanish at that vector space O_bar
    """
    F_q = O_bar.base_ring()
    m = len(Public_key)
    o = O_bar.ncols()
    v_random = sum(F_q.random_element()*O_bar.transpose()[i] for i in range(o))
    return [Eval(Public_key, O_bar.transpose()[i]) for i in range(o)]

def matrix_E(F_q, m, k):
    R = F_q['z']
    (z,) = R._first_ngens(1)

    Z = zero_matrix(R, k, k)
    idx = 0
    for i in range(k):
        for j in range(k-1, i-1, -1):
            Z.add_to_entry(i, j, z ** idx)
            if i != j: Z.add_to_entry(j, i, z ** idx)
            idx += 1

    det = Z.determinant()
    p_irr = R.irreducible_element(m)
    while det % p_irr == 0:
        p_irr = R.irreducible_element(m)

    c = companion_matrix(p_irr, format='right')
    return c


def Get_Mayo_Keys(n, m, o, k, q):
    """
    input:
    n = number of variables
    m = number of polynomials
    o = dimension of the Oil space
    k = number of UOV components in P_star
    q = size of the field F_q
    
    output:
    F_q = field of size q
    P = list with block matrices of the UOV part
    Public_key = list with public key matrices of the UOV part
    Public_key_polar = list with the polar form public key matrices of the UOV part
    P_star = whipped UOV map as a list of polynomials
    O = random matrix for the Oil space of size (n-o)xo
    O_bar = Oil space of the UOV map, matrix of size nxo
    E = constant matrix of size mxm over F_q that represents mult by z in F_q[z]/(f(z))
    """
    F_q, P, Public_key, Public_key_polar, O, O_bar = Get_UOV_Keys(n, m, o, q)
    E = matrix_E(F_q, m, k)
    return F_q, P, Public_key, Public_key_polar, O, O_bar, E

def Check_Oil_P_star(Public_key, E, O_bar):
    """
    input:
    Public_key = list with public key matrices of the UOV part
    E = constant matrix of size mxm over F_q that represents mult by z in F_q[z]/(f(z))
    O_bar = Oil space of the UOV map = [O | I_o]^T
    
    output:
    evaluation of the P_star polynomials at a random vector in O_bar^k
    to check that they all vanish at that vector
    """
    F_q = O_bar.base_ring()
    v_random = []
    for i in range(k):
        v_random += list(sum(F_q.random_element()*O_bar.transpose()[i] for i in range(o)))
    v_random = vector(v_random)
    return Eval_P_star(Public_key, E, v_random)

def P_star_theory(F_q, n, m, k, Public_key, Public_key_polar, E):
    """
    input:
    F_q = field of size q
    n = number of variables
    m = number of polynomials
    k = number of UOV components in P_star
    Public_key = list with public key matrices of the UOV part
    Public_key_polar = list with the polar form public key matrices of the UOV part
    E = constant matrix of size mxm over F_q that represents mult by z in F_q[z]/(f(z))
    
    output:
    P_star2_matrices = whipped UOV map as a list of matrices
    """
    
    E_matrices = {}
    w = 0
    for i in range(k):
        for l in range(k-1, i-1, -1):
            E_matrices[(i, l)] = E ** w
            w += 1
    
    P_star2_matrices = []
    for t in range(m):
        P_star2 = block_matrix([[zero_matrix(F_q, n, n) for j in range(k)] for i in range(k)])
        for l in range(k):
            matriz1 = sum(E_matrices[(l,l)][t,i]*Public_key[i] for i in range(m))
            P_star2[l*n:l*n+n, l*n:l*n+n] = matrix(matriz1)
            for j in range(l+1, k):
                matriz2 = sum(E_matrices[(l,j)][t,i]*Public_key_polar[i] for i in range(m))
                P_star2[l*n:l*n+n, j*n:j*n+n] = matrix(matriz2)          
        P_star2_matrices.append(P_star2)
    return P_star2_matrices

def Sign(P, O, E, t_document): 
    """
    input:
    P = list with block matrices of the UOV part
    O = random matrix for the Oil space of size (n-o)xo
    E = constant matrix of size mxm over F_q that represents mult by z in F_q[z]/(f(z))
    t_document = document in F_q^m to be signed
    
    output:
    signature = signature (in F_q^(n*k)) of t_document
    """
    
    F_q = O.base_ring()
    # Matrices of size (n-o)xo  
    L = [(PM[0]+PM[0].transpose())*O+PM[1] for PM in P]

    Firma = False
    intentos = 1
    while not Firma:
        V = random_matrix(F_q, k, n-o)
        M = []
        for i in range(k):
            matriz = zero_matrix(F_q, m, o)
            for j in range(m):
                matriz[j] = V[i] * L[j]
            M.append(matriz)

        A = zero_matrix(F_q, m, k*o)
        y = vector(t_document)
        l = 0

        for i in range(k):
            lista = list(range(i, k))
            lista.reverse()
            for j in lista:
                if i==j:
                    u = [V[i]*P[a][0]*V[i] for a in range(m)]
                else:
                    u = [V[i]*P[a][0]*V[j]+V[j]*P[a][0]*V[i] for a in range(m)]

                y -= (E**l) * vector(u)

                A[: , i*o:(i+1)*o] += (E**l)*M[j]
                if i!=j:
                    A[: , j*o:(j+1)*o] += (E**l)*M[i]
                l += 1

        try:
            x = A.solve_right(y)
            s = [0 for i in range(k*n)]
            for i in range(k):
                s[i*n : (i+1)*n] = list(V[i] + O*x[i*o : (i+1)*o])+list(x[i*o : (i+1)*o])

            break
        except ValueError:
            intentos += 1
    
    print(f"Number of tries = {intentos}")
    return s


def Eval_P_star(Public_key, E, signature):    
    """
    input:
    Public_key = list with public key matrices of the UOV part
    E = constant matrix of size mxm over F_q that represents mult by z in F_q[z]/(f(z))
    signature = vector in F_q^(n*k)
    
    output:
    y = Evaluation of P_star at signature
    """
    F_q = E.base_ring()
    n = Public_key[0].nrows()
    nk = len(signature)
    k = int(nk/n)

    s = []
    for i in range(k):
        s.append(vector(signature[i*n:(i+1)*n]))

    y = vector([F_q(0) for i in range(m)])
    l = 0

    for i in range(k):
        lista = list(range(i, k))
        lista.reverse()
        for j in lista:
            if i==j:
                u = [s[i]*Public_key[a]*s[i] for a in range(m)]
            else:
                u = [s[i]*Public_key[a]*s[j]+s[j]*Public_key[a]*s[i] for a in range(m)]

            y += (E**l) * vector(u)
            l += 1

    return y

def Verify(Public_key, E, t_document, signature): 
    """
    input:
    Public_key = list with public key matrices of the UOV part
    E = constant matrix of size mxm over F_q that represents mult by z in F_q[z]/(f(z))
    t_document = document in F_q^m to that was signed
    signature = vector in F_q^(n*k) that is a signature of t_document
    
    output:
    Determines if signature is a signature of t_document
    """
    y = Eval_P_star(Public_key, E, signature)
    return y==vector(t_document)


# # Examples

# In[2]:


# Parameters
from Mayo_parameters import *

Mayo_name = "mayo_1"
# Mayo_name = "mayo_2"
# Mayo_name = "mayo_3"
# Mayo_name = "mayo_5"
n = DEFAULT_PARAMETERS[Mayo_name]['n']
m = DEFAULT_PARAMETERS[Mayo_name]['m']
o = DEFAULT_PARAMETERS[Mayo_name]['o']
k = DEFAULT_PARAMETERS[Mayo_name]['k']
q = DEFAULT_PARAMETERS[Mayo_name]['q']

# n, m, o, k, q = (8, 5, 2, 3, 7)
# n, m, o, k, q = (8, 5, 2, 3, 2)
# n, m, o, k, q = 66, 64, 8, 9, 16
# n, m, o, k, q = 33, 32, 6, 6, 16

print("-----------------------------------------")
print("|                                       |")
print("|               Mayo                    |")
print("-----------------------------------------")
print(" ")
print(f"      {n=}, {m=}, {o=}, {k=}, {q=}")
print(" ")
print("-----------------------------------------")
print(" ")

# In[3]:


# Produce Mayo Keys
F_q, P, Public_key, Public_key_polar, O, O_bar, E = Get_Mayo_Keys(n, m, o, k, q)


# In[4]:


# Sanity Check: We now evaluate P_star at a random element in O^k
print("Sanity Check: We now evaluate P_star at a random element in O^k")
print(Check_Oil_P_star(Public_key, E, O_bar))
print(" ")

# In[5]:


# Random document
t_document = [F_q.random_element() for i in range(m)]

# Produce a signature for t_document
print("Producing a signature for t_document")
signature = Sign(P, O, E, t_document)


# In[6]:


# Verify the signature of t_document
print("Verify the signature of t_document")
print(Verify(Public_key, E, t_document, signature))
print(" ")


# In[7]:

# P_star_matrices according to Luis's pdf
P_star_matrices = P_star_theory(F_q, n, m, k, Public_key, Public_key_polar, E)

# Eval(P_star_matrices, vector(signature))
print("Evaluate P_star_matrices at signature and compare it with t_document")
print(Eval(P_star_matrices, vector(signature)) == vector(t_document))

