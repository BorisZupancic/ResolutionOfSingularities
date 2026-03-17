from sage.all import *
from sage.schemes.affine.affine_subscheme import AlgebraicScheme_subscheme_affine

class WeightedSubscheme(AlgebraicScheme_subscheme_affine):
    r"""
    A weighted center on an affine scheme.
    
    Representation of a weighted center on an affine scheme as a subscheme 
    with weights assigned to the defining functions.

    INPUT: 

    - ``A`` -- the ambient affine scheme
    - ``parameters`` -- the defining functions of the underlying subscheme (as a list)
    - ``invariant`` -- the invariant of the weighted center (a list of rationals assigned to each parameter)

    EXAMPLES::

        sage: A.<x,y> = AffineSpace(QQ,2)
        sage: Z = WeightedSubscheme(A, [x,y], [2,3])
        sage: Z.x
        [x,y]
        sage: Z.a
        [2,3]
        sage: Z.ambient_space()
        Affine Space of dimension 2 over Rational Field
    """
    
    def __init__(self, A, parameters, invariant):
        
        AlgebraicScheme_subscheme_affine.__init__(self,A,parameters)

        self.a = invariant
        self.x = parameters
        self.marking = lcm(
            ZZ(lcm(QQ(ai).denominator() for ai in  self.a) * aj) for aj in self.a
        )
        self.w = tuple(ZZ(self.marking/ai) for ai in self.a)
        
    def _repr_(self):
        r"""
        String representation of the object.
        """
        return (f"Weighted subscheme of {self.ambient_space()} defined by parameters {self.x} and invariant {self.a}")

    def _latex_(self):
        r"""
        LaTeX representation for show().
        """
        from sage.misc.latex import latex
        weighted_params = [rf"({latex(xx)})^{{{latex(aa)}}}" for xx, aa in zip(self.x, self.a)]
        params_str = ", ".join(weighted_params)
        return (rf"\text{{Weighted subscheme of }} {latex(self.ambient_space())} "
                rf"\text{{ defined by }} \mathbb{{Q}}\text{{-ideal }} "
                rf"({params_str})")
        
    @cached_method
    def F(self, n):
        r"""Returns the n-th ideal in the corresponding weight filtration on the coordinate ring."""
      
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
        
    #Define the corresponding valuation on the coordinate ring:
    def weighted_ord(self,I): 
        r"""The weighted order of vanishing of an ideal I at a point"""
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
                while g in self.F(order):
                    order += 1
                order -= 1 #compensation
            else:
                order = oo #Force it to be infinity
            
            orders.append(order)
        return min(orders)

    def is_admissible(self, I):
        r"""Determines if the weighted center is I-admissible using the criterion that the weighted order of I is equal to the marking of the center."""
        return self.weighted_ord(I) >= self.marking

    def codim(self):
        return len(self.x)

    def dim(self):
        n = self.ambient_space().dimension()
        return n - self.codim()

    def complete_parameters(self):   
        from sage.calculus.functions import jacobian
        
        A = self.ambient_space()
        X = A.coordinate_ring().gens() #standard coordinates
        Y = self.x #weighted parameters
        n = len(X) #ambient dimension
        l = len(Y)
        
        # Add algebraically independent coordinates one by one
        to_add = []
        if l < n:
            for g in X:
                if len(to_add)==n-l: break
                # Check if x_var is independent by testing the rank of the new Jacobian
                test_Y = Y + [g]
                if jacobian(test_Y, X).rank() == len(test_Y):
                    to_add.append(g)
        return Y + to_add

    def weight_of_multivector(self,xi, diagnostics=False):
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
            if diagnostics==True:
                U_to_V.display()
                
        #3. Compute the weights:
        component_weights = []
        for indices,coeff in xi.components(V.frame()).items():
            print(indices, " ",  coeff) if diagnostics==True else None
            w = self.weighted_ord(coeff) - sum([full_w[i] for i in indices])
            component_weights.append(w)
        
        return min(component_weights)



def weight_of_multivector_V0(Z,xi):
    from sage.calculus.functions import jacobian
    from sage.combinat.subset import Subsets
    
    A = Z.ambient_space()
    X = A.coordinate_ring().gens() #standard coordinates
    n = len(X) #dimension of the manifold
    k = xi.degree() #degree of the multivector

    #Have to complete Y = (y1,...,yl) to a system of coordinates (y1,...,yn)
    Y = Z.complete_parameters()
    #Note: have to manually set the weights of the new coordinates to zero (whatever they are)
    full_w = Z.w + tuple(0 for _ in range(n - len(Z.x)))

    #Now begin calculating weights of components of xi:
    J = jacobian(Y,X)
    
    component_weights= []
    index_combinations = Subsets(range(n),k) #indices 0 <= i_1 < ... < i_k <= n-1
    for rows in index_combinations:
        component = 0
        for cols in index_combinations:
            print(xi[*cols])
            minor = J.matrix_from_rows_and_columns(rows,cols).determinant()
            component += xi[*cols] * minor
        print(rows)
        print(component)
        w = Z.weighted_ord(component) - sum([full_w[i] for i in rows])
        print(w)
        component_weights.append(w)
    return min(component_weights)




