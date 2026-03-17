# from sage.all import show
from sage.all import *
from sage.combinat.subset import Subsets
from sage.calculus.functions import jacobian
from sage.rings.quotient_ring import QuotientRing_generic
# from sage.rings.ideals import Ideal_generic
# from sage.rings.polynomial.

#Restriction of an ideal I to a hypersurface defined by J:
def restrict(I,J): #equal to (I+J)/J in R/J
    r""" Compute the restriction of an R-ideal I to a subscheme V(J), i.e. compute the R/J-ideal (I+J)/J."""
    R = I.ring()
    A = R.quotient(J)
    I_return = A.ideal((I+J).gens())
    I_return = A.ideal(I_return.groebner_basis())
    return I_return

#Derivative of an ideal:
# def D(I):
#     R = I.ring()
#     Der = R.derivation_module()
    
#     G = I.gens()
#     dG = [v(g) for v in Der.gens() for g in G]
#     DI = R.ideal(G+dG)
#     DI = R.ideal(DI.groebner_basis())
#     return DI

def Diff(I):
    r"""Compute the derivative ideal of an ideal I."""
    A = I.ring()
    # Check if A is actually a quotient ring
    if hasattr(A, 'cover_ring'):
        R = A.cover_ring()
        J = A.defining_ideal()
        G = [g.lift() for g in I.gens()]
        
    else:
        # If A is already a polynomial ring, use it as the cover ring
        # and assume the defining ideal is zero.
        R = A
        J = R.ideal(0)
        G = I.gens()
    
    F = J.gens()
    X = R.gens()
    
    r = len(F)
    n = J.dimension() 
    N = len(X)

    Jacobian = jacobian(F, X)

    # Initialize to None to avoid ring mismatch on the first intersection
    I_return = R.ideal(1)

    row_combinations = Subsets(range(r), N-n)
    col_combinations = Subsets(range(N), N-n)
    
    for rows in row_combinations:
        for cols in col_combinations:
            M = Jacobian.matrix_from_rows_and_columns(rows, cols)
            
            # Use adjugate() instead of adjoint()
            C = M.adjugate().transpose()         
            h = M.det()
            # print(f"h={h}")
            # Skip if h is zero to avoid saturation errors
            if h == 0: continue

            Ders = []
            for g in G:
                for k in range(N):
                    if k not in cols:
                        Dk = h * g.derivative(X[k])
                        # Ensure we use .derivative() for multivariate polynomials
                        Dk -= sum([F[rows[i]].derivative(X[k]) * C[i, j] * g.derivative(X[cols[j]]) 
                                   for i in range(len(rows)) for j in range(len(cols))])
                        Ders.append(Dk)
            # show(Ders)
            I_M = R.ideal(G + F + Ders)
            saturated_ideal = I_M.saturation(h)[0] # saturation often returns (ideal, degree)
            # print(f"saturated ideal = {saturated_ideal}")
            if I_return is None:
                I_return = saturated_ideal
            else:
                I_return = I_return.intersection(saturated_ideal)
            # print(f"I_return = {I_return}")
    I_return = restrict(I_return,J)
    return I_return if I_return is not None else A.ideal(0)

def D_V2(I):
    r"""Compute the derivative ideal of an ideal I."""
    A = I.ring()
    # Check if A is actually a quotient ring
    if hasattr(A, 'cover_ring'):
        R = A.cover_ring()
        J = A.defining_ideal()
        G = [g.lift() for g in I.gens()]
    
    else:
        # If A is already a polynomial ring, use it as the cover ring
        # and assume the defining ideal is zero.
        R = A
        J = R.ideal(0)
        G = I.gens()
        
    DI = R.ideal([g.derivative(x) for g in G for x in R.gens()]) #take derivatives in cover
    DI = A.ideal(DI.gens()) #descend
    DI = A.ideal(DI.groebner_basis())
    return DI

#n^th Derivation of an ideal:
def Dn(I,n):
    r"""Compute the n-fold derivative ideal of an ideal I."""
    DI = I
    for i in range(n):
        DI = Diff(DI)
    return DI

#Derivation of an ideal I with respect to a multi-index b = (b1,...,bl) and parameters x = (x1,...,xj), where l <= j+1:
def Db(I,b,x):
    # R = I.ring()
    l = len(b)
    if l == 1:
        return Dn(I,b[0])
    else:
        J = Db(I,b[0:l-1],x) #recursive step
        J = restrict(J,x[l-2])
        return Dn(J,b[-1])

#Order of Vanishing of an Ideal at a point:
def ord(I,p):
    r"""Compute the order of vanishing of an ideal I at a point p."""

    # Check if we are in a quotient ring and get the cover ring
    R_quotient = I.ring()
    try:
        # For Quotient Rings
        R = R_quotient.cover_ring()
    except AttributeError:
        # For standard Polynomial Rings
        R = R_quotient
        
    X = R.gens()
    subs_dict = {X[i]: X[i] + p[i] for i in range(len(X))}
    
    gen_orders = []
    for g in I.gens():
        g = g.lift() if hasattr(g, 'parent') and isinstance(g.parent(), QuotientRing_generic) else g
        g_shifted = g.subs(subs_dict)
        if g_shifted.is_zero():
            continue
        
        # The order of a polynomial at the origin is the 
        # minimum total degree of its terms.
        # .dict().keys() gives us the exponent tuples, e.g., (2, 3) for x^2*y^3
        term_orders = [sum(exp) for exp in g_shifted.dict().keys()]
        gen_orders.append(min(term_orders))
    
    return min(gen_orders) if gen_orders else 0

#Maximal Order of Vanishing of an Ideal:
def maxord(I):
    r"""Compute the maximal order of vanishing of an ideal I."""
    R = I.ring()
                
    n = 0
    DnI = Dn(I,n)
    while DnI != DnI.ring().ideal(1):
        n+=1
        DnI = Dn(I,n)
    return n #-1 #over-incremented by 1 abovepy

def in_vanishing_set(I,p):
    R = I.ring()
    X = R.gens()

    point = {X[i]:p[i] for i in range(len(X))}
    return all(g.subs(point) == 0 for g in I.gens())
    
def is_smooth_at_point(I,p):
    # R = I.ring()
    # X = R.gens()
    # N = len(X)

    # point = {X[i]:p[i] for i in range(N)}

    #if at least one of the g in D(I) evaluates to som
    return not in_vanishing_set(Diff(I),p)
    
    # R = I.ring()
    # X = R.gens()
    # N = len(X)

    # Jac = jacobian(I.gens(),X)
    # # show(Jac)
    # Jac = Jac.subs({X[i]:p[i] for i in range(N)})
    # # show(Jac)
    # rank = Jac.rank()
    # codim = N - I.dimension()
    # # print(codim)
    # return True if rank == codim else False
    

#Maximal Contact of an Ideal at a point:
def maximal_contact(I,p):
    A = I.ring() 
    n = ord(I,p)
    if n == 0: #no maximal contact if ord(I) = 0
        return 
    else:
        for g in Dn(I,n-1).gens():
            G = A.ideal(g)
            print(G)
            if ord(Diff(G),p) == 0: #note: V(g) is smooth at p iff p not in V(g,dg) iff ord_p(<g,dg>) = 0
                return g.lift() if hasattr(A,'cover_ring') else g
            else:
                continue

#Maximal Contact of an Ideal:
def global_maximal_contact(I):
    A = I.ring()
    n = maxord(I)
    if n == 0: #no maximal contact if ord(I) = 0
        return 
    else:
        for g in Dn(I,n-1).gens():
            G = A.ideal(g)
            if maxord(Diff(G)) == 0: #note: V(g) is smooth iff V(g,dg) is empty iff maxord(<g,dg>) = 0
                return g.lift() if hasattr(A,'cover_ring') else g
            else:
                continue
