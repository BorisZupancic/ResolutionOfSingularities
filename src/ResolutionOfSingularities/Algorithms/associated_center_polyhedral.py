from sage.all import *
from ResolutionOfSingularities.Polyhedra import *
from ResolutionOfSingularities.Weightings import *
from ResolutionOfSingularities.IdealOperations import *

from sage.schemes.generic.algebraic_scheme import AlgebraicScheme_subscheme

def associated_center_polyhedral(Y:AlgebraicScheme_subscheme, verbose=False):
    r"""
    
    Compute the associated center of a subscheme of an affine scheme, :math:`Y \subset X`, using Newton- and admissible- polyhedra. 

    INPUT:

    - ``Y`` -- an instance of :class:`AlgebraicScheme_subscheme_affine`; the subscheme :math:`Y\subset X`.

    OUTPUT:

    - An instance of :class:`~ResolutionOfSingularties.Weightings.WeightedSubscheme`; the associated center :math:`Z^{\mathrm{as}}_\bullet(X,Y)`.


    EXAMPLES:: 

        sage: from ResolutionOfSingularities import *
        sage: X.<x,y,z> = AffineSpace(3,QQ)
        sage: Y = X.subscheme(x^2 + y^3)
        sage: Z = associated_center_polyhedral(Y); Z
        Weighted subscheme of Affine Space of dimension 3 over Rational Field defined by parameters [x, 3*y] and invariant [2, 3]
        
        sage: Y = X.subscheme(x^2 + y^2*z)
        sage: Z = associated_center_polyhedral(Y); Z
        Weighted subscheme of Affine Space of dimension 3 over Rational Field defined by parameters [x, y, z] and invariant [2, 3, 3]

    .. WARNING:: 
            
        This sometimes fails.

    EXAMPLES::

        sage: from ResolutionOfSingularities import *
        sage: X.<x,y> = AffineSpace(2,QQ)
        sage: Y = X.subscheme([(x+y^2)^2 + y^3])
        sage: Z = global_associated_center(Y); Z
        Weighted subscheme of Affine Space of dimension 2 over Rational Field defined by parameters [x, y] and invariant [2, 3]
        sage: try:
        ....:     Z = associated_center_polyhedral(Y)
        ....: except Exception as e:
        ....:     print(type(e),e)
        ....:
        <class 'ZeroDivisionError'> ring homomorphism not surjective


    """
    
    if not isinstance(Y,AlgebraicScheme_subscheme_affine):
        raise NotImplementedError

    ###############################################################
    # HELPER FUNCTIONS / SUB-ROUTINES 
    ###############################################################
    
    def Del(I,b,coords):
        R = I.ring()
        xx = R.gens()
        n = R.ngens()
        Jac = jacobian(coords, xx)
        caJ = Jac.inverse()

        for i in range(n):
            m = 0
            while m < b[i]:
                I = R.ideal([sum(
                        [caJ[j,i]*f.derivative(xx[j]) for j in range(n)]
                    ) for f in I.gens()])
                m+=1
        return I


    ###############################################################
    # ALGORITHM
    ###############################################################
    
    #INITIALIZATION:
    I = Y.defining_ideal()
    A = Y.ambient_space()
#set -g default-command "$SHELL" 
    R = A.coordinate_ring()
    Z = WeightedSubscheme(A,[],[])
    n = A.dimension()
    k = Z.codim()
    
    if verbose:
        print(f"STEP {k}:")
        print(rf"\Z^{ ({Z.codim()}) }_{{\bullet}} = {Z._latex_()}")
        print(rf"\mathrm{{ord}}_{{Z_\bullet}}(I) = {Z.weighted_ord(I)}")    
        print(f"Center is admissible: {Z.is_admissible(I)}")

    #RECURSION: Given Z^{j} ( non-admissible j-semi-associated center ), compute Z^{j+1} ( (j+1)-semi-associated center )
    while not Z.is_admissible(I) and Z.dim() > 0:
        k=Z.codim()
        if verbose:
            print("")
            print(f"STEP {k+1}:")
        
        #0. Preparatory stuff:
        #Complete parameters of Z:
        coords = Z.complete_parameters()
        
        #Compute the admissible polyhedron in the new coordinates:
        adm = AdmissiblePolyhedron(Y,coordinates=coords)
        if verbose:
            print(f"Admissible Polyhedron = {adm.Vrepresentation()}")
            
        #1: Compute w{j+1}
        w = [1/aa for aa in Z.a]
        eqns = [ [ -w[i] ] + [1 if i==j else 0 for j in range(n)] for i in range(k) ]
        #collect all (w1,...,wj,u,...,u) in adm into a polyhedron:
        p = (adm 
      #       & Polyhedron(eqns = eqns, ambient_dim=3) 
             & Polyhedron(vertices = [w + [0]*(n-k)], rays=[[0]*k + [1]*(n-k)])
        )
        if verbose:
            print(f"Polyhedron of possible (w1,...,w_k, u,...,u) = {p.Vrepresentation()}")
        coords = Z.complete_parameters()
        #take the vertex (w_1,...,w_j,u,...,u) in p with smallest u
        w_new = sorted(p.vertices_list(), key=lambda x: x[-1])[0]
        a = Z.a + [QQ(1/w_new[-1])] 
        if verbose:
            print(f"Smallest: {w_new}")
        print(f"New invariant: a = {a}") if verbose else None
           
        #2: Compute x{j+1}
        Newt_Y = NewtonPolyhedron(Y,coordinates=coords)[0]     
        betas = Newt_Y.vertices_list()
        beta = 0
        for b in betas:
            if vector(w_new).dot_product(vector(b))==1:
                beta = b 
                break
        
        f = 1 
        for g in I.gens():
            if Del(R.ideal(g),beta,coords) != R.ideal(0):
                f = g 
                break 

        b_ = beta
        for i in range(n-k):
            if b_[k+i] > 0: 
                b_[k+i] += -1
                break
        x = Z.x + [global_maximal_contact(Del(R.ideal(f),b_,coords)) / factorial(maxord(R.ideal(f)))] 
        print(f"New parameter: x = {x} )") if verbose else None
        
        #3: Redefine center
        Z = WeightedSubscheme(A,x,a)
        if verbose:  
            print(rf"\Z^{ ({Z.codim()}) }_{{\bullet}} = {Z._latex_()}")
            print(rf"\mathrm{{ord}}_{{Z_\bullet}}(I) = {Z.weighted_ord(I)}")    
            print(f"Center is admissible: {Z.is_admissible(I)}")
            
    return Z
