from sage.all import *
from ResolutionOfSingularities.Weightings import *
from ResolutionOfSingularities.IdealOperations import *

from sage.manifolds.differentiable.multivectorfield import MultivectorField
from sage.manifolds.differentiable.chart import DiffChart 
from sage.all import ZZ, QQ, VectorSpace, vector, Polyhedron, identity_matrix
from sage.schemes.generic.algebraic_scheme import AlgebraicScheme_subscheme

def NewtonPolyhedron(Y: AlgebraicScheme_subscheme, xi: MultivectorField = None, coordinates=None):
    r"""
    Compute the Newton polyhedron of a subscheme :math:`Y` and an optional multivector field :math:`\xi`,
    with respect to coordinates :math:`\mathbf{x}=(x_1,\dots,x_n)`. This is defined by:

    .. MATH::
       
            \mathrm{Newt}_Y &= \mathrm{conv}\{\beta\in\mathbb{Z}_{\geq 0}^n \mid c_\beta^l \neq 0\}, \\
            \mathrm{Newt}_\xi &= \mathrm{conv}\{\beta\in\mathbb{Z}_{\geq 0}^n \mid c_{\beta+e_i+e_j}^{ij} \neq 0\},

    where 
    
    .. MATH::
    
            Y &= \mathbf{V}\left(\sum_\beta c^1_\beta \mathbf{x}^\beta, \dots, \sum_\beta c^r_\beta \mathbf{x}^\beta\right),\\
            \xi &= \sum_{ij}\sum_\beta c^{ij}_\beta \mathbf{x}^\beta \partial_i\wedge\partial_j.

    INPUT:

    - ``Y`` -- :class:`~sage.schemes.generic.algebraic_scheme.AlgebraicScheme_subscheme`

    - ``xi`` -- :class:`~sage.manifolds.differentiable.multivectorfield.MultivectorField`
      (optional).  If provided, the Newton polyhedron of its coefficient
      polynomials is also computed.

    - ``coordinates`` -- a list or tuple of polynomials specifying the target
      coordinate system.  If ``None`` (default), the ambient coordinate ring
      generators are used.

    OUTPUT:

    A pair ``(p1, p2)`` consisting of:

        - ``p1`` -- :class:`sage.geometry.polyhedron.Polyhedron`, the Newton polyhedron of the defining ideal of ``Y``
    - ``p2`` -- :class:`sage.geometry.polyhedron.Polyhedron`, the Newton polyhedron of the coefficients of ``xi`` (or the empty polyhedron if ``xi`` is ``None``)

    EXAMPLES::

        sage: from ResolutionOfSingularities import *
        sage: A.<x,y> = AffineSpace(2,QQ)
        sage: Y = A.subscheme([x^2 + y^3, x*y - 1])
        sage: p1, p2 = NewtonPolyhedron(Y)
        sage: p1.vertices_list()
        [[0, 0], [0, 3], [2, 0]]

    EXAMPLES::

        sage: from ResolutionOfSingularities import *
        sage: A.<x,y,z> = AffineSpace(3,QQ)
        sage: Y = A.subscheme([x*y + z^2, x^2 - y*z])
        sage: p1, p2 = NewtonPolyhedron(Y)
        sage: p1.vertices_list()
        [[0, 0, 2], [0, 1, 1], [1, 1, 0], [2, 0, 0]]

    EXAMPLES (with a multivector field)::

        sage: from ResolutionOfSingularities import *
        sage: A.<x,y> = AffineSpace(2,QQ)
        sage: Y = A.subscheme([x^2 + y^2 - 1])
        sage: # Create a simple multivector field on A^2
        sage: U = Manifold(2, 'U')
        sage: X.<x,y> = U.chart()
        sage: xi = X.frame()[0]  
        sage: p1, p2 = NewtonPolyhedron(Y, xi)
        sage: p1  # Newton polyhedron of the curve
        A 2-dimensional polyhedron in ZZ^2 defined as the convex hull of 3 vertices

    
    EXAMPLES (with different coordinates)::

        sage: from ResolutionOfSingularities import *
        sage: A.<x,y> = AffineSpace(2,QQ)
        sage: Y = A.subscheme([x^2 + 2*x*y + y^2])
        sage: p1, p2 = NewtonPolyhedron(Y)
        sage: p1.Vrepresentation()
        (A vertex at (0, 2), A vertex at (2, 0))
        sage: p1, p2 = NewtonPolyhedron(Y,coordinates=[x+y,x-y])
        sage: p1.Vrepresentation()
        (A vertex at (2, 0),)

    .. WARNING::

        ``NewtonPolyhedron`` will fail if ``coordinates`` is a list/tuples of polynomials not defining an actual coordinate system. 
        i.e. if the Jacobian of the induced coordinate transformation is not invertible.

    """
    X = Y.ambient_space()
    R = X.coordinate_ring()
    n = R.ngens()

    #Prepare Coordinate Transformation:
    if coordinates is None:
        coordinates = R.gens()
    phi = R.hom(coordinates)
    psi = phi.inverse()
    #WARNING: This is sometimes NOT INVERTIBLE

    #Compute Newton Polyhedron of Y
    p1 = Polyhedron() 
    if Y is not None:
        vertices = []
        for f in Y.defining_ideal().gens():
            f = psi(f) #transform f into new coordinates
            for exp in f.exponents():
                vertices.append(exp)
        p1 = Polyhedron(vertices = vertices, base_ring=ZZ)

    #Compute Newton Polyhedron of xi
    #WARNING: THIS DOES NOT ACCOUNT FOR THE CHANGE OF BASE IN e[i]
    p2 = Polyhedron() 
    if xi is not None:
        e = VectorSpace(QQ,n).basis()
        #R = PolynomialRing(QQ, U[:])
        vertices = []
        for indices, coeff in xi.components().items():
            w = sum([e[i] for i in indices])
            coeff = psi(R(str(coeff))) #transform coefficient into new coordinates
            for exp in coeff.exponents():
                v = vector(exp) - w
                vertices.append(v)
        p2 = Polyhedron(vertices = vertices, base_ring=ZZ)
    return p1, p2

def AdmissiblePolyhedron(Y: AlgebraicScheme_subscheme, xi:MultivectorField = None, coordinates=None):
    r"""
    Compute the admissible polyhedron of a subscheme :math:`Y` and an optional multivector field :math:`\xi`, with respect to a system of coordinates :math:`\mathbf{x}=(x_1,\dots,x_n)`. 

    It is defined as the intersection of the admissible polyhedra of :math:`Y` and :math:`\xi`

    .. MATH::

        \mathrm{adm}(\mathbf{x}) = \mathrm{adm}_Y(\mathbf{x}) \cap \mathrm{adm}_\xi(\mathbf{x}) 

    which are defined in terms of the Newton Polyhedra by

    .. MATH::

            \mathrm{adm}_Y(\mathbf{x}) &= \{w\in\mathbb{Q}{\geq 0}^n \mid w \cdot \beta \geq 1, \  \forall \beta \in \mathrm{Newt}_Y(\mathbf{x})\} \\ 
            \mathrm{adm}_\xi(\mathbf{x}) &= \{w \in \mathbb{Q}_{\geq 0}^n \mid w\cdot \beta \geq 0, \ \forall \beta \in \mathrm{Newt}_\xi(\mathbf{x}) \}.

    In words, the admissible polyhedron of :math:`(Y,\xi)` is the convex polyhedral cone defined by the linear
    inequalities that encode the following three conditions:

    1. **Y-admissibility**: for every vertex ``v`` of the Newton polyhedron
       of ``Y``, the vector ``(-1, v)`` defines a facet of the cone;
    2. **xi-admissibility**: for every vertex ``v`` of the Newton polyhedron
       of ``xi``, the vector ``(0, v)`` defines a facet;
    3. **Non-negativity**: the standard basis vectors define facets ensuring
       all coordinate weights are non-negative.

    INPUT:

    - ``Y`` -- :class:`sage.schemes.generic.algebraic_scheme.AlgebraicScheme_subscheme`

    - ``xi`` -- :class:`sage.manifolds.differentiable.multivectorfield.MultivectorField`
      (optional). 

    - ``coordinates`` -- list or tuple; polynomials specifying the target
      coordinate system.  If ``None`` (default), the ambient coordinate ring
      generators are used.

    OUTPUT:

    A Sage :class:`~sage.geometry.polyhedron.Polyhedron` object representing
    the admissible polyhedron.

    EXAMPLES::

        sage: from ResolutionOfSingularities import *
        sage: A.<x,y> = AffineSpace(2,QQ)
        sage: Y = A.subscheme([x^2 + y^3])
        sage: P = AdmissiblePolyhedron(Y)
        sage: P.Hrepresentation()
        (An inequality (2, 0) x - 1 >= 0, An inequality (0, 3) x - 1 >= 0)

    EXAMPLES (with a vector field)::

        sage: from ResolutionOfSingularities import *
        sage: A.<x,y,z> = AffineSpace(3,QQ)
        sage: Y = A.subscheme([x^2 + y*z])
        sage: # Create a simple multivector field
        sage: U = Manifold(3, 'U'); X.<x,y,z> = U.chart(); e = X.frame()
        sage: xi = z*e[0] - (1/2)*e[1]
        sage: P = AdmissiblePolyhedron(Y, xi)
        sage: P.Vrepresentation()
        (A ray in the direction (0, 0, 1),
         A ray in the direction (1, 0, 1),
         A vertex at (1, 0, 1),
         A vertex at (1/2, 0, 1))


    EXAMPLES (with different coordinates)::

        sage: from ResolutionOfSingularities import *
        sage: A.<x,y> = AffineSpace(2,QQ)
        sage: Y = A.subscheme([x^2 + y^2])
        sage: #Use a linear change of coordinates
        sage: u = x + y
        sage: v = x - y
        sage: P = AdmissiblePolyhedron(Y, coordinates=[u,v])
        sage: P.Hrepresentation()
        (An inequality (2, 0) x - 1 >= 0, An inequality (0, 2) x - 1 >= 0)
        sage: P.Vrepresentation()
        (A ray in the direction (0, 1),
         A ray in the direction (1, 0),
         A vertex at (1/2, 1/2))

    """
    n = Y.ambient_space().ngens()
    Newt_Y, Newt_xi = NewtonPolyhedron(Y, xi, coordinates)
    M1 = [[-1] + v for v in Newt_Y.vertices_list()] #Y-admissibility
    M2 = [[0] + v for v in Newt_xi.vertices_list()] #xi-admissibiliy
    M3 = [[0] + list(row) for row in identity_matrix(n)] #non-negativity of coordinate weights
    return Polyhedron(ieqs = M1 + M2 + M3)
