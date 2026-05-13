from sage.all import *
from sage.combinat.subset import Subsets
from sage.calculus.functions import jacobian
from sage.rings.quotient_ring import QuotientRing_generic

def restrict(I,J): #equal to (I+J)/J in R/J
    r"""
    Compute the restriction of an :math:`R`-ideal :math:`I` to a subscheme :math:`V(J):= \mathrm{Spec}(R/J)`, 
    i.e. compute the :math:`R/J`-ideal

    .. MATH::
        I\vert_{V(J)} = (I+J)/J.

    INPUT:

    - ``I`` -- an ideal (of some ring ``R = I.ring()``).
    - ``J`` -- another ideal (of the same ring ``R``).

    OUTPUT:

    - A :class:`sage.rings.ideals.Ideal_generic` equal to ``(I+J)/J``.

    EXAMPLES::

        sage: from ResolutionOfSingularities.IdealOperations import restrict
        sage: R.<x,y,z> = PolynomialRing(QQ,3)
        sage: I = R.ideal(x^2 + y^2 - z^2)
        sage: J = R.ideal(z-1)
        sage: restrict(I,J)
        Ideal (xbar^2 + ybar^2 - 1) of Quotient of Multivariate Polynomial Ring in x, y, z over Rational Field by the ideal (z - 1)
    """
    R = I.ring()
    A = R.quotient(J)
    I_return = A.ideal((I+J).gens())
    I_return = A.ideal(I_return.groebner_basis())
    return I_return

def Diff(I, n=1):
    r"""
    Compute the :math:`n^\text{th}` derivative ideal :math:`\mathcal{D}^{\leq n} I` of an ideal :math:`I` of 
    an :math:`R`-algebra :math:`A = R[x_1,\dots,x_m]`. This
    is defined by the recursion

    .. MATH::

        \mathcal{D}^{\leq n} I = \mathcal{D}\left(\mathcal{D}^{\leq n - 1} I \right)
    
    where 

    .. MATH::
        
        \mathcal{D}^{\leq 1} I = I + \langle \xi(I) \mid \xi \in \mathrm{Der}_R(A,A) \rangle.

    If :math:`A` is a polynomial ring, this is computed using ``.derivation_module``. If :math:`A` is a quotient 
    of a polynomial ring, this is computed using the algorithm ``Diff`` of [Lee2020]_.
    
    INPUT:

    - ``I`` -- an ideal of a :class:`sage.rings.polynomial.multi_polynomial_ideal.MPolynomialIdeal` or :class:`sage.rings.quotient_ring.QuotientRing_generic_with_category` 
    - ``n`` -- integer (default: ``1``); the number of times to differentiate
    
    OUTPUT:
        
    - An ideal as an instance of :class:`sage.rings.ideals.Ideal_generic`.

    EXAMPLES::
        
        sage: from ResolutionOfSingularities.IdealOperations import Diff
        sage: R.<x,y,z> = PolynomialRing(QQ,3)
        sage: I = R.ideal(x*y*z)
        sage: Diff(I)
        Ideal (x*y, x*z, y*z) of Multivariate Polynomial Ring in x, y, z over Rational Field
        sage: Diff(I,2)
        Ideal (x, y, z) of Multivariate Polynomial Ring in x, y, z over Rational Field
        sage: Diff(I,3)
        Ideal (1) of Multivariate Polynomial Ring in x, y, z over Rational Field

        sage: Diff(I,0)==I 
        True
        sage: Diff(I)==Diff(I,1)
        True

    REFERENCES:

    .. [Lee2020] J. Lee,
       *Algorithmic resolution via weighted blowings up*,
       :arxiv:`2008.02169`
    """
    if n == 0:
        return I
    if n > 1:
        return Diff(Diff(I), n-1)

    A = I.ring()

    # Case 1: A is a polynomial ring
    if not hasattr(A, 'cover_ring'):
        Der = A.derivation_module()
        dI = A.ideal([v(g) for v in Der.gens() for g in I.gens()])
        DI = I + dI
        DI = A.ideal(DI.groebner_basis())
        return DI

    #Case 2: A is a quotient of a polynomial ring
    R, J = A.cover_ring(), A.defining_ideal()
    G = [g.lift() for g in I.gens()]
        
    X, F = R.gens(), J.gens()
    
    r = len(F)
    dim = J.dimension() 
    N = len(X)

    Jacobian = jacobian(F, X)

    I_return = R.ideal(1)

    row_combinations = Subsets(range(r), N-dim)
    col_combinations = Subsets(range(N), N-dim)
    
    for rows in row_combinations:
        for cols in col_combinations:
            M = Jacobian.matrix_from_rows_and_columns(rows, cols)
            C = M.adjugate().transpose()         
            h = M.det()
            # Skip if h is zero to avoid saturation errors
            if h == 0: continue

            Ders = []
            for g in G:
                for k in range(N):
                    if k not in cols:
                        Dk = h * g.derivative(X[k]) - sum(
                            [F[rows[i]].derivative(X[k]) * C[i, j] * g.derivative(X[cols[j]]) 
                            for i in range(len(rows)) for j in range(len(cols))]
                        )
                        Ders.append(Dk)
            I_M = R.ideal(G + F + Ders)
            saturated_ideal = I_M.saturation(h)[0] # saturation often returns (ideal, degree)
            
            I_return = I_return.intersection(saturated_ideal)

    I_return = restrict(I_return,J)
    return I_return if I_return is not None else A.ideal(0)

def Db(I,b,x):
    r"""
    Compute the ideal :math:`\mathcal{D}[I;\vec{\beta};\vec{x}]` defined in [Brais2025]_ 
    in the following way. Let :math:`R` be a commutative ring, :math:`A` be an `R`-algebra, :math:`I\lhd A` be an ideal, 
    :math:`\vec{x} = (x_1,\dots,x_j)` a tuple of algebraically independent elements of :math:`A`. 
    For each tuple :math:`\vec{\beta} = (\beta_1,\dots,\beta_l)` with :math:`l\leq j+1`, we define the recursion
    
    .. MATH::
    
        \mathcal{D}[\vec{\beta}] := \mathcal{D}[I;\vec{\beta};\vec{x}] := \mathcal{D}^{\leq \beta_l} \left( \mathcal{D}[(\beta_1,\dots,\beta_{l-1})] \vert_{V(x_{l-1})} \right)
    
    where if :math:`j=0` and :math:`l=1`, then

    .. MATH::
        
        \mathcal{D}[\vec{\beta}] = \mathcal{D}[I; (\beta_1); ()] := \mathcal{D}^{\leq \beta_1} I .

    INPUT: 

    - ``I`` -- an ideal (as an instance of ``sage.ring.ideal.Ideal_generic``) 
    - ``b`` -- a tuple or list of integers 
    - ``x`` -- a tuple or list of algebraically independent elements of ``A = I.ring()`` 
 
    OUTPUT:

    - An ideal as an instance of ``sage.rings.ideals.Ideal_generic``. 

    EXAMPLES::
        
        sage: from ResolutionOfSingularities.IdealOperations import *
        sage: R.<x,y,z,w> = PolynomialRing(QQ,4)
        sage: I = R.ideal(x*y*z + y*z*w)
        sage: Db(I,[0,1],[x])
        Ideal (ybar*zbar, ybar*wbar, zbar*wbar) of Quotient of Multivariate Polynomial Ring in x, y, z, w over Rational Field by the ideal (x)
        sage: Db(I,[0,1,1],[x,y])
        Ideal (zbar, wbar) of Quotient of Multivariate Polynomial Ring in x, y, z, w over Rational Field by the ideal (y, x)
    
    REFERENCES:
    
    .. [Brais2025] M. Brais,
       *Streamlining resolution of singularities with weighted blow-ups*,
       :arxiv:`2512.01859`

    """
    l = len(b)
    if l == 1:
        return Diff(I,b[0])
    else:
        J = Db(I,b[0:l-1],x) #recursive step
        J = restrict(J,x[l-2])
        return Diff(J,b[-1])

def ord(I,p):
    r"""
    Compute the order of vanishing of an ideal :math:`I \lhd A=R[x_1,\dots,x_n]` at a point
    :math:`p \in \mathrm{Spec}(A)`.

    This is defined as:

    .. MATH::

        \mathrm{ord}_p(I) := \min_{f \in I \setminus \{0\}} \mathrm{ord}_p(f),

    where :math:`\mathrm{ord}_p(f)` is the order of vanishing of :math:`f` at :math:`p`,
    i.e. the minimum total degree of :math:`f` after translating :math:`p` to
    the origin.

    INPUT:

    - ``I`` -- an ideal of a polynomial ring or quotient ring
    - ``p`` -- a point of the ambient space, given as a list or tuple of
      coordinates

    OUTPUT:

    - A non-negative integer.

    EXAMPLES::

        sage: from ResolutionOfSingularities.IdealOperations import ord
        sage: A.<x,y> = PolynomialRing(QQ, 2)
        sage: I = A.ideal(x^2 + y^3)
        sage: ord(I, [0, 0])
        2
        sage: ord(I, [1, -1])
        1    
        sage: ord(I, [1, 1])
        0
    """

    #1. Check if we are in a quotient ring and get the cover ring:
    A = I.ring()
    try:
        R = A.cover_ring() # For Quotient Rings
    except AttributeError:
        R = A # For standard Polynomial Rings
    
    #2. Define translation of polynomials to point p:
    X = R.gens()
    subs_dict = {X[i]: X[i] + p[i] for i in range(len(X))}
   
    #3. Collect orders of generators of I:
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
    
    #4. Return the minimum of the collected orders:
    return min(gen_orders) if gen_orders else 0

#Maximal Order of Vanishing of an Ideal:
def maxord(I):
    r"""
    Compute the maximal order of vanishing of an ideal :math:`I\lhd A=R[x_1,\dots,x_n]`. 
    This is by definition
    
    .. MATH::

        \mathrm{maxord}(I) := \max_{p\in \mathrm{Spec}(A)}\mathrm{ord}_p(I),

    but it can be computed as

    .. MATH:: 

        \mathrm{maxord}(I) = \inf \{a \in \mathbb{N}\cup \{0\} \mid \mathcal{D}^{\leq a} I = A = \langle 1 \rangle \}.
    
    INPUT:

    - ``I`` -- an ideal of a polynomial ring or quotient ring 
    
    OUTPUT:

    - An integer (as a python ``int``).

    EXAMPLES::
        
        sage: from ResolutionOfSingularities.IdealOperations import *
        sage: A.<x,y> = PolynomialRing(QQ,2)
        sage: I = A.ideal(x^2 + y^3)
        sage: maxord(I)
        2
    """

    A = I.ring()
                
    a = 0
    DnI = Diff(I,a)
    while DnI != DnI.ring().ideal(1):
        a+=1
        DnI = Diff(I,a)
    return a 

def in_vanishing_set(I,p):
    r"""
    Determine if a poinResolutionOfSingularities.t :math:`p\in \mathrm{Spec}(A)` is in the vanishing set of an ideal :math:`I\lhd A`.
    This is true if and only if 

    .. MATH::

        \forall f \in I \colon \ f(p) = 0.  

    INPUT:

    - ``I`` -- an ideal of a polynomial ring or quotient ring
    - ``p`` -- a point in the ambient space, given as a list or tuple of coordinates

    OUTPUT:

    - boolean; ``True`` if :math:`p\in V(I)`, ``False`` otherwise.

    EXAMPLES::

        sage: from ResolutionOfSingularities.IdealOperations import *
        sage: A.<x,y> = PolynomialRing(QQ, 2)
        sage: I = A.ideal(x^2 + y^3)
        sage: in_vanishing_set(I, [0, 0])
        True
        sage: in_vanishing_set(I, [1,-1])
        True
        sage: in_vanishing_set(I, [1, 0])
        False
    """
    A = I.ring()
    X = A.gens()
    point = {X[i]:p[i] for i in range(len(X))}
    return all(g.subs(point) == 0 for g in I.gens())
    
def is_smooth_at_point(I,p):
    r"""        
    Determine if the vanishing set of an ideal :math:`I\lhd A` is smooth at a point :math:`p\in \mathrm{Spec}(R)`.
    This is true if and only if :math:`op\not\in V(\mathcal{D}^{\leq 1} I)`.

    INPUT:

    - ``I`` -- an ideal
    - ``p`` -- a point 

    OUTPUT:

    - boolean; ``True`` if the ideal is smooth at the point, ``False`` otherwise.
    """
    return not in_vanishing_set(Diff(I),p)
    

def maximal_contact(I,p):
    r"""
    Compute an element of maximal contact to an ideal :math:`I\lhd A=R[x_1,\dots,x_n]` at a point :math:`p\in\mathrm{Spec}(A)`.
    By definition, an element :math:`x\in I` is of *maximal contact to :math:`I` at :math:`p`* if and only if 
    :math:`x(p) = 0` and the hypersurface :math:`V(x)\subset \mathrm{Spec}(A)` is smooth at :math:`p`.

    A maximal contact to :math:`I` at :math:`p` exists if and only if :math:`\mathrm{ord}_p(I) \geq 1`. 

    INPUT:

    - ``I`` -- an ideal of a polynomial ring or quotient ring
    - ``p`` -- a point in the ambient space, given as a list or tuple of coordinates

    OUTPUT:

    - An element of ``I`` representing the maximal contact at ``p``, if it exists; otherwise ``None``.

    """
    A = I.ring() 
    a = ord(I,p)
    if a == 0: #no maximal contact if ord(I) = 0
       return  
    else:
        for g in Diff(I,a-1).gens():
            G = A.ideal(g)
            if ord(Diff(G),p) == 0: #note: V(g) is smooth at p iff p not in V(g,dg) iff ord_p(<g,dg>) = 0
                return g.lift() if hasattr(A,'cover_ring') else g
            else:
                continue

#Maximal Contact of an Ideal:
def global_maximal_contact(I):
    r"""
    Compute an element of maximal contact to an ideal :math:`I`.
    By definition, an element :math:`x\in I` is of *maximal contact to :math:`I`* if and only if 
    the hypersurface :math:`V(x)\subset \mathrm{Spec}(A)` is smooth at :math:`p`.

    A maximal contact to :math:`I` exists if and only if :math:`\mathrm{maxord}(I) \geq 1`. 

    INPUT:

    - ``I`` -- an ideal of a polynomial ring or quotient ring

    OUTPUT:

    - An element of ``I`` representing the maximal contact, if it exists; otherwise ``None``.

    """
    A = I.ring()
    a = maxord(I)
    if a == 0: #no maximal contact if ord(I) = 0
        return 
    else:
        for g in Diff(I,a-1).gens():
            G = A.ideal(g)
            if maxord(Diff(G)) == 0: #note: V(g) is smooth iff V(g,dg) is empty iff maxord(<g,dg>) = 0
                return g.lift() if hasattr(A,'cover_ring') else g
            else:
                continue
