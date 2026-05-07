from sage.all import *
from sage.schemes.affine.affine_subscheme import AlgebraicScheme_subscheme_affine

class WeightedSubscheme(AlgebraicScheme_subscheme_affine):
    r"""
    A weighted subscheme :math:`Z_\bullet=(x_1^{a_1},\dots,x_k^{a_k})` of an affine scheme :math:`X = \mathrm{Spec}(R)`.
    
    INPUT: 

    - ``X`` -- a :class:`sage.schemes.affine.affine_space.AffineSpace_generic` representing the ambient affine scheme :math:`X`
    - ``parameters`` -- a list ``[x1,...,xk]`` of elements of ``X.coordinate_ring()`` representing the defining functions of the weighted subscheme :math:`Z_\bullet = (x_1^{a_1},\dots,x_k^{a_k})`
    - ``invariant`` -- a list ``[a1,...,ak]`` of rationals representing the invariant :math:`(a_1,\dots,a_k) = \mathrm{inv}(Z_\bullet)`

    EXAMPLES::

        sage: from ResolutionOfSingularities.Weightings import *
        sage: A.<x,y> = AffineSpace(QQ,2)
        sage: Z = WeightedSubscheme(A, [x,y], [2,3])
        sage: Z.x
        [x, y]
        sage: Z.a
        [2, 3]
        sage: Z.ambient_space()
        Affine Space of dimension 2 over Rational Field
    """
    
    def __init__(self, X, parameters, invariant):
        
        AlgebraicScheme_subscheme_affine.__init__(self,X,parameters)

        self.x = parameters
        self.a = invariant
        self.marking = lcm(
            ZZ(lcm(QQ(ai).denominator() for ai in  self.a) * aj) for aj in self.a
        )
        self.w = tuple(ZZ(self.marking/ai) for ai in self.a)
        
    def _repr_(self):
        r"""
        String representation of the :class:`WeightedSubscheme`.

        EXAMPLE:: 

            sage: from ResolutionOfSingularities.Weightings import *
            sage: A.<x,y> = AffineSpace(QQ,2)
            sage: Z = WeightedSubscheme(A, [x,y], [2,3])
            sage: Z
            Weighted subscheme of Affine Space of dimension 2 over Rational Field defined by parameters [x, y] and invariant [2, 3]
        """
        return (f"Weighted subscheme of {self.ambient_space()} defined by parameters {self.x} and invariant {self.a}")

    def _latex_(self):
        r"""
        LaTeX representation the :class:`WeightedSubscheme`.
        """
        from sage.misc.latex import latex
        weighted_params = [rf"({latex(xx)})^{{{latex(aa)}}}" for xx, aa in zip(self.x, self.a)]
        params_str = ", ".join(weighted_params)
        return (rf"\text{{Weighted subscheme of }} {latex(self.ambient_space())} "
                rf"\text{{ defined by }} \mathbb{{Q}}\text{{-ideal }} ({params_str})")
        
    def codim(self):
        r"""
        The codimension of the underlying subscheme. If :math:`Z_\bullet=(x_1^{a_1},\dots,x_k^{a_k})`, then this is :math:`\mathrm{codim}(Z_\bullet) = k`.
        
        EXAMPLE:: 

            sage: from ResolutionOfSingularities.Weightings import *
            sage: A.<x,y> = AffineSpace(QQ,2)
            sage: Z = WeightedSubscheme(A, [x,y], [2,3])
            sage: Z.codim()
            2 
        """
        return len(self.x)

    def dim(self):
        r"""
        The dimension of the underlying subscheme. If :math:`Z_\bullet=(x_1^{a_1},\dots,x_k^{a_k})`, then this is :math:`\mathrm{dim}(Z_\bullet) = n - k`.
        
        EXAMPLE:: 

            sage: from ResolutionOfSingularities.Weightings import *
            sage: A.<x,y> = AffineSpace(QQ,2)
            sage: Z = WeightedSubscheme(A, [x,y], [2,3])
            sage: Z.dim()
            0
        """
        return self.ambient_space().dimension() - self.codim()

    def complete_parameters(self):  
        r"""
        Complete the defining parameters of :math:`Z_\bullet = (x_1^{a_1},\dots,x_k^{a_k})`
        to a system of parameters :math:`x_1,\dots,x_k,y_{k+1},\dots,y_n` for the ambient space :math:`X = \mathrm{Spec}(R)`, where :math:`n` is the 
        ambient dimension.

        EXAMPLES::
            
            sage: from ResolutionOfSingularities.Weightings import *
            sage: X.<x,y,z> = AffineSpace(QQ, 3)
            sage: Z = WeightedSubscheme(X, [x, y], [2, 3]) 
            sage: Z.complete_parameters()
            [x, y, z]
        """
        from sage.calculus.functions import jacobian
        
        R = self.ambient_space().coordinate_ring()
        G, n = R.gens(), R.ngens(),  #standard coordinates, ambient dimension
        
        # Add algebraically independent coordinates one by one
        parameters = [*self.x]
        for g in G:
            if len(parameters)==n: break 
            # if g is independent from the current parameters, add it to the list
            if jacobian(parameters+[g], G).rank() == len(parameters)+1:
                parameters.append(g)
        return parameters 

    @cached_method
    def weight_filtration(self, n):
        r"""
        The n-th level of the corresponding weight filtration on the coordinate ring.
        
        EXAMPLE::

            sage: from ResolutionOfSingularities.Weightings import *
            sage: X.<x,y> = AffineSpace(QQ, 2)
            sage: Z = WeightedSubscheme(X, [x, y], [2, 3]) 
            sage: for n in range(5):
            ....:     Z.weight_filtration(n)
            ....:
            Ideal (1) of Multivariate Polynomial Ring in x, y over Rational Field
            Ideal (x, y) of Multivariate Polynomial Ring in x, y over Rational Field
            Ideal (x, y) of Multivariate Polynomial Ring in x, y over Rational Field
            Ideal (y^2, x) of Multivariate Polynomial Ring in x, y over Rational Field
            Ideal (x^2, x*y, y^2) of Multivariate Polynomial Ring in x, y over Rational Field
        """
      
        k = len(self.w)
        bounds = [n // w + 1 for w in self.w]
        generator_powers = []
        for p in cartesian_product([range(b+1) for b in bounds]):
            if sum(p[i]*self.w[i] for i in range(k)) >= n:
                generator_powers.append(p)
        
        gens = []
        for p in generator_powers:
            gen = 1
            for i in range(k):
                gen = gen*(self.x[i]**p[i])
            gens.append(gen)

        A = self.ambient_space()
        R = A.coordinate_ring()
        Fn = R.ideal(R.ideal(gens).groebner_basis())
        return Fn
        
    def weighted_ord(self,I): 
        r"""
        The weighted order of vanishing of an ideal or polynomial :math:`I`.
        
        EXAMPLE::

            sage: from ResolutionOfSingularities.Weightings import *
            sage: X.<x,y> = AffineSpace(QQ, 2)
            sage: Z = WeightedSubscheme(X, [x, y], [2, 3]) 
            sage: Z.weighted_ord(x*y)
            5
            sage: Z.weighted_ord(y^3 + x^2)
            6
            sage: I = X.coordinate_ring().ideal(x*y, y^3 + x^2)
            sage: Z.weighted_ord(I)
            5
        """
        # 1. Check if 'I' is an Ideal or a single element
        if hasattr(I, 'gens'):
            generators = I.gens()
        else:
            generators = [I]
        
        from sage.all import oo
        orders = []
        for g in generators:
            if g != 0:
                order = 0
                while g in self.weight_filtration(order):
                    order += 1
                order -= 1 #compensation
            else:
                order = oo #Force it to be infinity
            
            orders.append(order)
        return min(orders)

    def weight_of_multivector(self,xi):
        #0. Access some variables for later:
        n = self.ambient_space().dimension() #dimension of ambient space
        M = xi.domain() #The manifold that xi is defined on
        
        #1. Complete the weighted coordinates (y1,...,yl) to a full system of coordinates (y1,...,yn):
        Y = self.complete_parameters()
        #... and manually set the weights of the new coordinates to zero:
        full_w = self.w + tuple(0 for _ in range(n - len(self.x)))
    
        #2. Coordinate Transformation from standard coords to weighted coords:
        coord_names = " ".join(f"y_{i}" for i in range(1, n + 1)) #The names of the weighted coordinates
        V = next((c for c in M.atlas() if c[:]==coord_names), None) #First check if it exists already (it will be a global variable)
        if V is None:
            U = M.default_chart() #The standard coordinates
            V = M.chart(coord_names) #The weighted coordinates
            U_to_V = U.transition_map(V, Y) #The transition functions
                
        #3. Compute the weights:
        component_weights = []
        for indices,coeff in xi.components(V.frame()).items():
            w = self.weighted_ord(coeff) - sum([full_w[i] for i in indices])
            component_weights.append(w)
        
        return min(component_weights)

    def is_admissible(self, I):
        r"""
        Determines if the weighted center is I-admissible using the criterion that the weighted order of I is equal to the marking of the center.
        """
        return self.weighted_ord(I) >= self.marking


    def is_Poisson_admissible(self, pi):
        r"""
        Determines if the weighted center is :math:`\pi`-admissible, with respect to some multivector :math:`\pi \in \mathfrak{X}_X^k` (usually a Poisson structure). 
        By definition, this is true if and only if  

        .. MATH:: 

            \mathrm{ord}_{Z_\bullet}(\pi) \geq 0. 
        
        """
        return self.weight_of_multivector(pi) >= 0
