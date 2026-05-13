from sage.all import *
from ResolutionOfSingularities.Scrap.Polyhedra import *
from ResolutionOfSingularities.Weightings import *
from ResolutionOfSingularities.IdealOperations import *

def local_associated_center_polyhedral(Y, ReportStatus=False):
    
    if not isinstance(Y,AlgebraicScheme_subscheme_affine):
        raise NotImplementedError

    ###############################################################
    # HELPER FUNCTIONS / SUB-ROUTINES 
    ###############################################################

    def beta(a : list[Rational], x : list[Rational]) -> list[Rational]:
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
    n = A.dimension()
    Z = WeightedSubscheme(A,[],[])
    
    if ReportStatus:
        step = Z.codim()
        print(f"STEP {step}:")
        print(rf"\Z^{ ({Z.codim()}) }_{{\bullet}} = {Z._latex_()}")
        print(rf"\mathrm{{ord}}_{{Z_\bullet}}(I) = {Z.weighted_ord(I)}")    
        print(f"Center is admissible: {Z.is_admissible(I)}")

    #RECURSION: Given Z^{j} ( non-admissible j-semi-associated center ), compute Z^{j+1} ( (j+1)-semi-associated center )
    while not Z.is_admissible(I) and Z.dim() > 0: 
        if ReportStatus == True:
            step += 1
            print("")
            print(f"STEP {step}:")
        
        #0. Preparatory stuff:
        #Complete parameters of Z:
        coords = Z.complete_parameters()
        chart = ???
        
        #Compute the admissible polyhedron in the new coordinates:
        adm = AdmissiblePolyhedron(Y,None,chart)
            
        #1: Compute w{j+1}
        w = Z.w
        eqns = [ [ -w[i] ] + [1 if i==j else 0 for j in range(n)] for i in range(len(w)) ]
        #collect all (w1,...,wj,u,...,u) in adm into a polyhedron:
        p = (adm 
             & Polyhedron(eqns = eqns) 
             & Polyhedron(rays=[w + [0]*(n-len(w)) ,  
                                [0]*len(w) + [1]* (n-len(w)) ])
        )
        #take the vertex (w_1,...,w_j,u,...,u) in p with smallest u
        w_new = sorted(p.vertices_list(), key=lambda x: x[-1])[0]
        a = Z.a + [QQ(1/w_new[-1])] 
        print(f"New invariant: a = {a}") if ReportStatus else None
            
        #4: Compute x{j+1}
        b_ = beta(a,x)
        b_[-1] += -1
        x = Z.x + [global_maximal_contact(Db(I,b_,Z.x))]
        print(f"New parameter: x = {Z.x} (maximal contact of: {Db(I,b_,Z.x).gens()})") if ReportStatus else None
        
        #SUB-STEP 5: Redefine center
        Z = WeightedSubscheme(A,x,a)
        if ReportStatus:  
            print(rf"\Z^{ ({Z.codim()}) }_{{\bullet}} = {Z._latex_()}")
            print(rf"\mathrm{{ord}}_{{Z_\bullet}}(I) = {Z.weighted_ord(I)}")    
            print(f"Center is admissible: {Z.is_admissible(I)}")
            
    return Z
