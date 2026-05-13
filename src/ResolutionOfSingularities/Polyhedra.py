from sage.all import *
from ResolutionOfSingularities.Weightings import *
from ResolutionOfSingularities.IdealOperations import *
import numpy as np


from sage.manifolds.differentiable.multivectorfield import MultivectorField
from sage.manifolds.differentiable.chart import DiffChart
from sage.all import QQ, VectorSpace, vector, PolynomialRing, Polyhedron
from sage.geometry.newton_polygon import NewtonPolygon 

def NewtonPolyhedron(Y: AlgebraicScheme_subscheme_affine, xi: MultivectorField, U: DiffChart):
    p1 = NewtonPolygon([]) 
    if Y is not None:
        vertices = []
        for f in Y.defining_ideal().gens():
            for exp in f.exponents():
                vertices.append(vector(exp))
        p1 = NewtonPolygon(vertices)

    p2 = NewtonPolygon([]) 
    if xi is not None:
        e = VectorSpace(QQ,xi.domain().dim()).basis()
        R = PolynomialRing(QQ, U[:])
        vertices = []
        for indices, coeff in xi.components().items():
            w = sum([e[i] for i in indices]) 
            for exp in R(str(coeff)).exponents():
                v = vector(exp) - w
                vertices.append(v)
        p2 = NewtonPolygon(vertices)
    return p1, p2

def AdmissiblePolyhedron(Y: AlgebraicScheme_subscheme_affine, xi:MultivectorField, U:DiffChart):
    n = Y.ambient_space().ngens()
    Newt_Y, Newt_xi = NewtonPolyhedron_V2(Y,xi, U)
    M1 = [[-1] + list(v) for v in Newt_Y.vertices()] #Y-admissibility
    M2 = [[0] + list(v) for v in Newt_xi.vertices()] #xi-admissibiliy
    M3 = [[0] + [1 if i==j else 0 for i in range(n)] for j in range(n)] #non-negativity of coordinate weights
    return Polyhedron(ieqs = M1 + M2 + M3)

