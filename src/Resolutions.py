from sage.all import *
from sage.all import QQ, ceil, Rational, PolynomialRing, diff
from .IdealOperations import *
from .Weightings import *
import numpy as np

def local_associated_center(Y, p, ReportStatus = False):
    r"""
    Compute the local associated weighted center of Y at point p.
    ...
    """      
    
    def Delta(b,a):  
        return np.sum(b/a)
        
    def Xi(b,a):    
        return QQ(b[-1] / (1 - sum([QQ(bb/aa) for bb, aa in zip(b[:-1],a)]) )) #result has to be rational

    def generate_betas(a,x):
        #Step (i): Compute  b = (b1,...,bj) such that \sum_{i=1}^j bi/ai < 1
        grid = np.meshgrid(*[np.arange(0,int(ceil(ai+1))) for ai in a], indexing='ij') #construct a grid: (0,...,a1) x ... x (0,...,aj)
        B = np.stack(grid, axis=-1).reshape(-1, len(grid)) #construct an arrayf of each b = (b1, ..., bj) in the grid
        B = [b for b in B if Delta(b,a)<1]
        
        #Step (ii): Compute b = (b1,...,bj,b{j+1}) such that Db(I,b,x) = <1>
        # For fixed (b1,...,bj) already computed above, loop through b{j+1}= 0, 1, ... until Db(I,b,x) = <1>,
        # The b{j+1} that you stop at will minimize Xi(b,a) = b{j+1} / (1 - sum_k bk/ak)
        bad_indices = []
        for i in range(len(B)): 
            b_temp = np.append(B[i], 1) #take B[i] = (b1,...,bj) and let b_temp = (b1,...,bj,0)
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
    
    #Initialization:
    if ReportStatus == True:
        step = 1
        print("STEP 1:")
        print("Initializing Center...")

    I = Y.defining_ideal()
    A = Y.ambient_space() #ambient_space
    # a = [ord(I,p)]
    # x = [maximal_contact(I,p)]
    Z = WeightedSubscheme(A,[maximal_contact(I,p)],[ord(I,p)])
    
    if ReportStatus==True:
        print(f"a = {Z.a}")
        print(f"x = {Z.x}")
        print(f"Center is admissible: {Z.is_admissible(I)}")
        print(f"wt(I) = {Z.weighted_ord(I)}")
        
    #RECURSION: Given (non-admissible) j-semi-associated center (a,x) = ((a1,...,aj), (x1,...,xj)), compute the (j+1)-semi-associated center
    while not Z.is_admissible(I): 
        
        if ReportStatus == True:
            step += 1
            print("")
            print(f"STEP {step}:")
            
        #SUB-STEP 1: Compute all b = (b1,...,bj,b{j+1}) such that \sum_{i=1}^j bi/ai < 1 and Db(I,b,x) = <1>
        B = generate_betas(Z.a,Z.x)
        
        if ReportStatus == True:
            print("Possible betas: B = ", B)
    
        
        #SUB-STEP 2: Compute the minimizer b and associated a{j+1} 
        if ReportStatus == True:
            print("Computing next entry in invariant...")
            
        Xi = [Xi(b,Z.a) for b in B]
        index = np.argmin(Xi)
        b = B[index]
        a = Z.a + [Xi[index]]

        if ReportStatus == True:
            print(f"Minimizer: b = {b}")
            print(f"New invariant: a = {a}")
        
        #SUB-STEP 3: Compute maximal contact
        b_ = b
        b_[-1] += -1
        
        if ReportStatus == True:
            print(f"Computing maximal contact of: {Db(I,b_,Z.x).gens()} ...")
            print(f"... maximal contact is: {maximal_contact(Db(I,b_,Z.x),p)}")
            
        x = Z.x + [maximal_contact(Db(I,b_,Z.x),p)]

        #SUB-STEP 4: Redefine center
        Z = WeightedSubscheme(A,x,a)
        
        if ReportStatus == True:
            print(f"New parameters: x = {Z.x}")
            
            print(f"New center is admissible: {Z.is_admissible(I)}")
            print(f"wt(I) = {Z.weighted_ord(I)}")
            
    return Z

def local_associated_center_V2(Y, p, ReportStatus = False):
    r"""
    Compute the local associated center of Y at point p.
    ...
    """      
        
    # INITIAL DATA
    A = Y.ambient_space() #ambient_space
    P1 = A.coordinate_ring()
    R = A.base_ring()
    n = P1.ngens()
    I = Y.defining_ideal()
    if ReportStatus == True:
        print(f"Computing Associated Center at p={p} of ideal:")
        show(I)
        print("")
    
    ###############################################################
    # HELPER FUNCTIONS / SUB-ROUTINES 
    ###############################################################
    def Delta(b : list[Rational], a : list[Rational]) -> Rational:  
        return QQ(sum([b[i]/a[i] for i in range(len(a))]))
        
    def Xi(b : list[Rational], a : list[Rational]) -> Rational: 
        return QQ( sum(b[len(a):]) / (1 - Delta(b,a)) )
    
    def coordinate_ring_transformation(Z):
        P2 = PolynomialRing(R,'y',n)

        yy = Z.complete_parameters() 
        #NOTE: these need to be parameters that vanish at p;
        # shift them manually if needed:
        for i in range(n):
            if yy[i](p)!=0:
                yy[i] = yy[i] - p[i]
                
        phi = P2.hom(yy, P1) #a homomorphism that writes y_i = y_i (x_1,...,x_n)
        show(phi)
        return phi.inverse()

    def betas(Z) -> list[list[Rational]]: 
        phi = coordinate_ring_transformation(Z)
        B = []
        for f in I.gens():
            F = phi(f) # Expand f in parameters (x_1,...,x_j,y_{j+1},...,y_n)
            B += [list(exp) for exp, coeff in F.dict().items() if coeff!=0 and Delta(exp,Z.a) < 1]
        return B
    
    def derivative(f,x,b):
        if b==0:
            return f
        else:
            return diff(derivative(f,x,b-1),x)

    def derivatives(f,xx,bb):
        if bb == []:
            return f
        else:
            return derivative(derivatives(f,xx[1:],bb[1:]),xx[0],bb[0])

    def x_new(Z,b):
        phi = coordinate_ring_transformation(Z)
        show(phi)
        psi = phi.inverse()
        yy = phi.codomain().gens() #Z.complete_parameters()
        
        for f in I.gens():
            F = phi(f)
            if derivatives(F,yy,b)(p) !=0:
                #Compute b_bar = (b_1,...,b_{l-1},b_l-1, b_{l+1}, ...) where l s.t b_l > 0
                b_bar = b
                l = n-1
                while b[l] == 0:
                    l -= 1
                b_bar[l] += -1
                
                return psi(derivatives(F,yy,b_bar))

    ###############################################################
    # ALGORITHM
    ###############################################################

    #Initialization:
    if ReportStatus == True:
        step = 0
        print(f"STEP {step}:")
        print("Initializing Center...")
    
    Z = WeightedSubscheme(A,[],[])
        
    if ReportStatus==True:
        print(f"a = {Z.a}")
        print(f"x = {Z.x}")
        print(f"Center is admissible: {Z.is_admissible(I)}")
        print(f"wt(I) = {Z.weighted_ord(I)}")

    #RECURSION: Given (non-admissible) j-semi-associated center (a,x) = ((a1,...,aj), (x1,...,xj)), compute the (j+1)-semi-associated center
    while not Z.is_admissible(I) and len(Z.x) < n: 
        
        #SUB-STEP 1: Compute the set B
        if ReportStatus == True:
            step += 1
            print("")
            print(f"STEP {step}:")
        B = betas(Z)
        if ReportStatus == True:
            print("Possible betas: B = ", B)
            print(f"Xi(B) = {[Xi(b, Z.a) for b in B]}")
        
        #SUB-STEP 2: Compute the minimizer b  
        b = B[np.argmin([Xi(b,Z.a) for b in B])]
        if ReportStatus == True:
            print(f"Minimizer: b = {b}")

        #SUB-STEP 3: Compute new entry of invariant a{j+1}
        if ReportStatus == True:
            print("Computing next entry in invariant...")
        a = Z.a + [Xi(b,Z.a)]
        if ReportStatus == True:
            print(f"New invariant: a = {a}")

        #SUB-STEP 4: Compute new parameter x{j+1} 
        x = Z.x + [x_new(Z,b)]
        if ReportStatus == True:
            print(f"New parameters: x = {x}")

        #SUB-STEP 4: Redefine center
        Z = WeightedSubscheme(A,x,a)
        if ReportStatus == True:
            print(f"New center is admissible: {Z.is_admissible(I)}")
            print(f"wt(I) = {Z.weighted_ord(I)}")

    return Z


# Construct the Global Associated Center of a (sub)scheme Y < X
def global_associated_center(Y, ReportStatus = False):
    
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
    
    #Initialization:
    if ReportStatus == True:
        step = 0
        print(f"STEP {step}:")
        print("Initializing Center...")

    I = Y.defining_ideal()
    A = Y.ambient_space()
    Z = WeightedSubscheme(A,[],[])
    
    if ReportStatus==True:
        print(f"a = {Z.a}")
        print(f"x = {Z.x}")
        print(f"Center is admissible: {Z.is_admissible(I)}")
        print(f"wt(I) = {Z.weighted_ord(I)}")    
        
    #RECURSION: Given (non-admissible) j-semi-associated center, compute (j+1)-semi-associated center
    while not Z.is_admissible(I) and Z.dim() > 0: 
        if ReportStatus == True:
            step += 1
            print("")
            print(f"STEP {step}:")
            
        #SUB-STEP 1: Compute all b = (b1,...,bj,b{j+1}) such that \sum_{i=1}^j bi/ai < 1 and Db(I,b,x) = <1>
        B = betas(Z.a,Z.x)
        if ReportStatus == True:
            print("Possible betas: B = ", B)

        #SUB-STEP 2: Compute the minimizer of B
        b = B[np.argmin([Xi(b,Z.a) for b in B])]
        if ReportStatus == True:
            print(f"Minimizer: b = {b}")
        
        #SUB-STEP 3: Compute a{j+1} 
        if ReportStatus == True:
            print("Computing next entry in invariant...")
        a = Z.a + [Xi(b,Z.a)]
        if ReportStatus == True:
            print(f"New invariant: a = {a}")
        
        #SUB-STEP 4: Compute maximal contact
        b_ = b
        b_[-1] += -1
        if ReportStatus == True:
            print(f"Computing maximal contact of: {Db(I,b_,Z.x).gens()} ...")    
        x = Z.x + [global_maximal_contact(Db(I,b_,Z.x))]
        if ReportStatus == True:
            print(f"New parameter: x = {Z.x}")
        
        #SUB-STEP 5: Redefine center
        Z = WeightedSubscheme(A,x,a)
        if ReportStatus == True:  
            print(f"New center is admissible: {Z.is_admissible(I)}")
            print(f"wt(I) = {Z.weighted_ord(I)}")
            
    return Z

# Construct the Poisson Associated Center of a Poisson (sub)scheme Y < X
def poisson_associated_center(Y, sigma, ReportStatus = False):
    
    I = Y.defining_ideal()
    A = Y.ambient_space()
    R = A.coordinate_ring()
    
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
    
    def kronecker(i,j):
        return 1 if i==j else 0

    def Delta_pi(s,i,a):
        #return sum([ ( s[j] - sum([kronecker(ii,j) for ii in i]) ) / a[j] kronecker for j in range(len(a))])
        vec = [sum([kronecker(ii,j) for ii in i]) for j in range(len(a))]
        return Delta(s,a) - Delta(vec,a)

    def Xi_pi(s,i,a):
        l = len(s)-1           
        denominator = - Delta_pi(s[:l],i,a[:l])
        numerator = s[l] - sum([kronecker(ii,l) for ii in i])
        return QQ(numerator/denominator)

    def multi_indices(a,x):
        if len(a)!=0:
            #first collect possible multi-indices for multivector-field basis:
            k = sigma.degree()
            n = A.dimension()
            S = []
            for i in Subsets(range(n),k):
                vec = [sum([kronecker(ii,j) for ii in i]) for j in range(len(a))]
                scale = Delta(vec,a)
                grid = np.meshgrid(*[ np.arange(0,int(ceil(a[j]*scale + 1))) for j in range(len(a)) ], indexing='ij') 
                grid = np.stack(grid, axis=-1).reshape(-1, len(grid)) #construct an array of each b = (b1, ..., bj) in the grid
                grid = grid.tolist()
                S += [[s,i] for s in grid if Delta_pi(s,i,a)<0]
        else:
            S = [[]]
        
        bad_indices = []
        for index in range(len(S)): 
            s, i = S[index]
            s_temp = s + [1]
            
            #grab the correct monomial in sigma:
            coeff = R.ideal(sigma[i].expr())

            DbI = Db(coeff,s_temp,x)
            if not DbI.is_zero(): #DbI != DbI.ring().zero():
                while not DbI.is_one(): #DbI != DbI.ring().ideal(1):        
                    s_temp[-1] += 1 #increment s{j+1} by 1
                    DbI = Db(coeff,s_temp,x) #recalculate
                S[index] = [s_temp,i] #replace S[index]
            else:
                bad_indices += [index]
                continue 
                
        #remove the bad (s,i):
        bad_indices.sort(reverse=True)
        for i in bad_indices:
            S.pop(i)

        return S

    ###############################################################
    # ALGORITHM
    ###############################################################
    
    #Initialization:
    if ReportStatus == True:
        step = 0
        print("")
        print(f"STEP {step}:")
        print("Initializing Center...")

    Z = WeightedSubscheme(A,[],[])
    
    if ReportStatus==True:
        print(f"a = {Z.a}")
        print(f"x = {Z.x}")
        print(f"Center is I-admissible: {Z.is_admissible(I)}")
        print(f"Center is pi-admissible: {(Z.weight_of_multivector(sigma) >= 0)}")
        print(f"wt(I) = {Z.weighted_ord(I)}")  
        print(f"wt(pi) = {Z.weight_of_multivector(sigma)}")  
        
    #RECURSION: Given (non-admissible) j-semi-associated center, compute (j+1)-semi-associated center
    while not (Z.is_admissible(I) and Z.weight_of_multivector(sigma) >= 0) and Z.dim() > 0: 
        if ReportStatus == True:
            step+=1
            print(f"STEP {step}:")
            
            
        if Z.weight_of_multivector(sigma)>=0 and not Z.is_admissible(I):
            #SUB-STEP 1: Compute all b = (b1,...,bj,b{j+1}) such that \sum_{i=1}^j bi/ai < 1 and Db(I,b,x) = <1>
            B = betas(Z.a,Z.x)
            if ReportStatus == True:
                print("Possible betas: B = ", B)
            #SUB-STEP 2: Compute the minimizer of B
            b = B[np.argmin([Xi(b,Z.a) for b in B])]
            if ReportStatus == True:
                print("Minimizer: b = ", b)
            #SUB-STEP 3: Compute a{j+1} 
            a = Z.a + [Xi(b,Z.a)]
            #SUB-STEP 4: Compute maximal contact
            b_ = b
            b_[-1] += -1
            x = Z.x + [global_maximal_contact(Db(I,b_,Z.x))]

        if Z.weight_of_multivector(sigma)<0 and Z.is_admissible(I):
            #SUB-STEP 1: Compute all b = (b1,...,bj,b{j+1}) such that \sum_{i=1}^j bi/ai < 1 and Db(I,b,x) = <1>
            S = multi_indices(Z.a,Z.x)
            if ReportStatus==True:
                print(f"Possible (s;I): S = {S}")
                
            #SUB-STEP 2: Compute the minimizer of S
            s,i = S[np.argmin([Xi_pi(s,i,Z.a) for s,i in S])]
            if ReportStatus==True:
                print(f"Minimizer (s;I) = {s,i}")
                
            #SUB-STEP 3: Compute a{j+1} 
            a = Z.a + [Xi_pi(s,i,Z.a)]
            #SUB-STEP 4: Compute maximal contact
            s_ = s
            s_[-1]+= -1
            coeff = R.ideal(sigma[i].expr())
            x = Z.x + [global_maximal_contact(Db(coeff,s_,Z.x))]
        
        if Z.weight_of_multivector(sigma)<0 and not Z.is_admissible(I):
            #Calculate both of the above:
            
            B = betas(Z.a,Z.x)
            if ReportStatus==True:
                print(f"Possible betas: B = {B}")
            b = B[np.argmin([Xi(b,Z.a) for b in B])]
            if ReportStatus == True:
                print("Minimizer: b = ", b)
            a1 = Z.a + [Xi(b,Z.a)]
            b_ = b
            b_[-1] += -1
            x1 = Z.x + [global_maximal_contact(Db(I,b_,Z.x))]
            
            S = multi_indices(Z.a,Z.x)
            if ReportStatus==True:
                print(f"Possible (s;I): S = {S}")
            s,i = S[np.argmin([Xi_pi(s,i,Z.a) for s,i in S])]
            if ReportStatus==True:
                print(f"Minimizer (s;I) = {s,i}")
            a2 = Z.a + [Xi_pi(s,i,Z.a)]
            s_ = s
            s_[-1]+= -1
            coeff = R.ideal(sigma[i].expr())
            x2 = Z.x + [global_maximal_contact(Db(coeff,s_,Z.x))]

            # Take one with smallest exponent a
            if a1[-1] <= a2[-1]:
                a = a1
                x = x1
            else:
                a = a2
                x = x2

        #SUB-STEP 5: Redefine center
        Z = WeightedSubscheme(A,x,a)
        
        if ReportStatus==True:
            print(f"a = {Z.a}")
            print(f"x = {Z.x}")
            print(f"Center is I-admissible: {Z.is_admissible(I)}")
            print(f"Center is pi-admissible: {(Z.weight_of_multivector(sigma) >= 0)}")
            print(f"wt(I) = {Z.weighted_ord(I)}")  
            print(f"wt(pi) = {Z.weight_of_multivector(sigma)}")  

    return Z
