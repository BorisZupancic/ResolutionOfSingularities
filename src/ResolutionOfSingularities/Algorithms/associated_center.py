from sage.all import *
from ResolutionOfSingularities.IdealOperations import *
from ResolutionOfSingularities.Weightings import *
import numpy as np

def global_associated_center(Y, verbose=False):
    r"""
    Compute the associated center of a subscheme of an affine scheme, :math:`Y \subset X`, using the `Method 2` of [Brais2025].

    INPUT:

    - ``Y`` -- an instance of :class:`AlgebraicScheme_subscheme_affine`; the subscheme :math:`Y\subset X`.

    OUTPUT:

    - An instance of :class:`~ResolutionOfSingularities.Weightings.WeightedSubscheme`; the associated center :math:`Z^{\mathrm{as}}_\bullet(X,Y)`.

    EXAMPLES::
    
        sage: from ResolutionOfSingularities import *
    
    **EXAMPLE 1: Cusp**

    ::
        
        sage: X.<x,y> = AffineSpace(QQ,2)
        sage: n = 5; Y = X.subscheme(x^2 + y^n)
        sage: Z = global_associated_center(Y); Z
        Weighted subscheme of Affine Space of dimension 2 over Rational Field defined by parameters [x, y] and invariant [2, 5]

    **EXAMPLE 2: Double Cusp**

    ::
        
        sage: X.<x,y> = AffineSpace(QQ,2)
        sage: xTilde, yTilde = x+x^2, y
        sage: Y = X.subscheme(xTilde^2 + yTilde^3)
        sage: Z = global_associated_center(Y); Z
        Weighted subscheme of Affine Space of dimension 2 over Rational Field defined by parameters [x^2 + x, y] and invariant [2, 3]

    **EXAMPLE 3: Whitney Umbrella**

    ::
        
        sage: X.<x,y,z> = AffineSpace(QQ,3)
        sage: Y = X.subscheme(x^2 + y^2*z)
        sage: Z = global_associated_center(Y); Z
        Weighted subscheme of Affine Space of dimension 3 over Rational Field defined by parameters [x, y, z] and invariant [2, 3, 3]

    **EXAMPLE 4: Normal Crossings Divisor**

    ::
        
        sage: X.<x,y,z> = AffineSpace(QQ,3)
        sage: Y = X.subscheme(x*y*z)
        sage: Z = global_associated_center(Y); Z
        Weighted subscheme of Affine Space of dimension 3 over Rational Field defined by parameters [x, y, z] and invariant [3, 3, 3]

    **EXAMPLE 5: Two Normal Crossings Divisors**

    ::
        
        sage: X.<x,y,z> = AffineSpace(QQ,3)
        sage: Y = X.subscheme(x*y*z + x)
        sage: Z = global_associated_center(Y); Z
        Weighted subscheme of Affine Space of dimension 3 over Rational Field defined by parameters [y*z + 1, x] and invariant [2, 2]

    **EXAMPLE 6: Three Normal Crossings Divisors**

    ::
        
        sage: X.<x,y,z,w> = AffineSpace(QQ,4)
        sage: Y = X.subscheme(x*y*z*w + x*y)
        sage: Z = global_associated_center(Y); Z 
        Weighted subscheme of Affine Space of dimension 4 over Rational Field defined by parameters [z*w + 1, x, y] and invariant [3, 3, 3]

    REFERENCES:
    
    .. [Brais2025] M. Brais,
       *Streamlining resolution of singularities with weighted blow-ups*,
       :arxiv:`2512.01859`
    
    """
    
    if not isinstance(Y,AlgebraicScheme_subscheme_affine):
        raise NotImplementedError

    ###############################################################
    # HELPER FUNCTIONS / SUB-ROUTINES 
    ###############################################################
    def Delta(b : list[Rational], a : list[Rational]) -> Rational:  
        return QQ(sum([bb/aa for aa,bb in zip(a,b)]))
        
    def Xi(b : list[Rational], a : list[Rational]) -> Rational:    
        return QQ(b[-1] / ( 1 - Delta(b[:-1],a) ))
        
    def betas(a : list[Rational], x : list[Rational]) -> list[Rational]:
        #Step (i): Compute  b = (b1,...,bj) such that \sum_{i=1}^j bi/ai < 1
        if len(a)!=0: #construct a grid: (0,...,a1) x ... x (0,...,aj)
            grid = np.meshgrid(*[np.arange(0,int(ceil(ai+1))) for ai in a], indexing='ij') 
            B = np.stack(grid, axis=-1).reshape(-1, len(grid)) #construct an array of each b = (b1, ..., bj) in the grid
            B = B.tolist()
            B = [b for b in B if Delta(b,a)<1]
        else:
            B = [[]]
        
        #Step (ii): Compute b = (b1,...,bj,b{j+1}) such that Db(I,b,x) = <1>
        # For fixed (b1,...,bj) already computed above, loop through b{j+1}= 0, 1, ... until Db(I,b,x) = <1>,
        # The b{j+1} that you stop at will minimize Xi(b,a) = b{j+1} / (1 - sum_k bk/ak)
        bad_indices = []
        for i in range(len(B)): 
            b_temp = B[i] + [1]
            DbI = Db(I,b_temp,x)
            if not DbI.is_zero(): #DbI != DbI.ring().zero():
                while not DbI.is_one(): #DbI != DbI.ring().ideal(1):        
                    b_temp[-1] += 1 #increment b{j+1} by 1
                    DbI = Db(I,b_temp,x) #recalculate
                B[i] = b_temp #replace B[i]
            else:
                bad_indices += [i]
                continue 
                
        #remove the bad (b1,...,bj):
        bad_indices.sort(reverse=True)
        for i in bad_indices:
            B.pop(i)

        return B

    ###############################################################
    # ALGORITHM
    ###############################################################
    
    #INITIALIZATION:
    I = Y.defining_ideal()
    A = Y.ambient_space()
    Z = WeightedSubscheme(A,[],[])
    
    if verbose:
        step = Z.codim()
        print(f"STEP {step}:")
        print(rf"\Z^{ ({Z.codim()}) }_{{\bullet}} = {Z._latex_()}")
        print(rf"\mathrm{{ord}}_{{Z_\bullet}}(I) = {Z.weighted_ord(I)}")    
        print(f"Center is admissible: {Z.is_admissible(I)}")

    #RECURSION: Given Z^{j} ( non-admissible j-semi-associated center ), compute Z^{j+1} ( (j+1)-semi-associated center )
    while not Z.is_admissible(I) and Z.dim() > 0: 
        if verbose == True:
            step += 1
            print("")
            print(f"STEP {step}:")
            
        #1: Compute all b = (b1,...,bj,b{j+1}) such that \sum_{i=1}^j bi/ai < 1 and Db(I,b,x) = <1>
        B = betas(Z.a,Z.x)
        print(f"Possible betas: B = {B}") if verbose else None 
            
        #2: Compute the minimizer of Xi(B)
        b = B[np.argmin([Xi(b,Z.a) for b in B])]
        print(f"Minimizer: b = {b}") if verbose else None
        
        #3: Compute a{j+1} 
        a = Z.a + [Xi(b,Z.a)]
        print(f"New invariant: a = {a}") if verbose else None
            
        #4: Compute x{j+1}
        b_ = b
        b_[-1] += -1
        J = Db(I,b_,Z.x)
        x = Z.x + [global_maximal_contact(J)]
        print(f"New parameter: x = {x} (maximal contact of: {J.gens()})") if verbose else None
        
        #5: Redefine center
        Z = WeightedSubscheme(A,x,a)
        if verbose:  
            print(rf"\Z^{ ({Z.codim()}) }_{{\bullet}} = {Z._latex_()}")
            print(rf"\mathrm{{ord}}_{{Z_\bullet}}(I) = {Z.weighted_ord(I)}")    
            print(f"Center is admissible: {Z.is_admissible(I)}")
            
    return Z
