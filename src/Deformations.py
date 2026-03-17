from sage.all import *
import numpy as np

def theta_matrix(L):
    n = L.ncols()
    B = L.inverse()
    Theta = np.zeros((n,n,n), dtype=object)
    for i in range(n):
        for j in range(i+1,n):
            for k in range(n):
                if k!=i and k!=j and B[i,j] != 0:
                    # Theta[i,j,k] = var(f"theta{i+1}{j+1}{k+1}") #(B[j,k] + B[k,i]) / B[i,j]  #var(f"theta{i}{j}{k}")
                    Theta[i,j,k] = (B[j,k] + B[k,i]) / B[i,j]
    return Theta


def deformed_bivector(L,A):
    n = L.ncols()
    B = L.inverse()
    Theta = theta_matrix(L)

    M = Manifold(n, 'M') 
    coords = ' '.join([f'x{i+1}' for i in range(n)])
    X = M.chart(coords)
    pi = M.multivector_field(2)
    for i in range(n):
        for j in range(i+1,n):
            sigma = A[i,j]
            for k in range(n):
                if k!=i and k!=j and B[i,j]!=0 and Theta[i,j,k] >= 0 and Theta[i,j,k] in ZZ: #take the colored edges only
                    sigma = sigma*X[k]**Theta[i,j,k]
            pi[i,j] = (L[i,j]*X[i]*X[j] + sigma)
            pi[j,i] = -pi[i,j]
            
    return pi