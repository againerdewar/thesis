from sage.all import *
import sys

# Take arguments from the command line
args = sys.argv

assert len(args) == 2

nval = int(args[1])


p = SymmetricFunctionAlgebra(QQ, basis="power")
x = PowerSeriesRing(QQ, 'x').gen()

Zx = p[1]

Z2 = SymmetricGroup(2)
e = Z2.identity()
t = Z2.an_element()

def gf_pleth(f, gf):
    partmapper = lambda part: prod(gf.subs({x:x^i}) for i in part)
    return p._apply_module_morphism(f, partmapper)

def unlabeled(f):
    partmapper = lambda part: x^(part.size())
    return p._apply_module_morphism(f, partmapper)

def labeled(f):
    def partmapper(part):
        if part.length() == part.size():
            return x^(part.length())
        else:
            return 0
    return p._apply_module_morphism(f, partmapper)

def plethystic_inverse(f, n):
        '''
        Return an approximate plethystic inverse of f: that is,
        a SymmetricFunction F such that f(F) = F(f) = 1, up to 
        some specified degree
        '''
        
        parent = f.parent()
        
        fstripped = f - f.restrict_degree(1, exact=True)
        
        improver = lambda F, i: Zx - fstripped.restrict_degree(i, exact=False).plethysm(F).restrict_degree(i, exact=False)
        
        finv = Zx
        
        for i in xrange(2, n+1):
            finv = improver(finv, i)
        
        return finv

def pointed(f):
    return Zx*f.derivative_with_respect_to_p1()

def Ze(n):
    return balanced_sum(1/part.aut() * prod(p[l] for l in part) for i in xrange(1,n+1) for part in Partitions(i))

def Zcon(n):
    return plethystic_inverse(Ze(n), n)

def union( mu, nu):
    return Partition(sorted(mu.to_list() + nu.to_list(), reverse=true))

def partmult( mu, n ):
    return Partition([part * n for part in mu.to_list()])

def efixedbcgraphs( mu, nu ):
    return 2^(sum([gcd(i, j) for i in mu for j in nu]))

def tfixedbcgraphs( mu ):
    return 2^(len(mu) + sum([integer_ceil(p/2) for p in mu]) + sum([gcd(mu[i], mu[j]) for i in range(0, len(mu)) for j in range(i+1, len(mu))]))

def Zbc( z2elt, n ):
    assert z2elt in Z2
    if z2elt == Z2.identity():
        return add([efixedbcgraphs(pair[0], pair[1]) * p(union(pair[0],pair[1])) / (pair[0].aut() * pair[1].aut()) for i in range(1, n+1) for pair in PartitionTuples(i, 2).list()])
    else:
        return add([tfixedbcgraphs( mu ) * p(partmult(mu, 2))/partmult(mu, 2).aut() for i in range(1, integer_floor(n/2)+1) for mu in Partitions(i).list() ])

def Zcbc( z2elt, n ):
    assert z2elt in Z2
    if z2elt == Z2.identity():
        return Zcon(n).plethysm(Zbc(e, n)).restrict_degree(n, exact=False)
    else:
        scale_part = lambda n: lambda m: m.__class__([i*n for i in m])
        pn_pleth = lambda f, n: f.map_support(scale_part(n))
        f = lambda part: prod(pn_pleth(Zbc(t^i, n), i) for i in part)
        return p._apply_module_morphism(Zcon(n),f).restrict_degree(n, exact=False)

def Zcbp( n ):
    return 1/2 * (Zcbc(e, n) + Zcbc(t, n))

def Zbp( n ):
    return Ze(n).plethysm(Zcbp(n)).restrict_degree(n, exact=False)

def Znbp_ogf( n ):
    Zcbp_ci = Zcbp(n)
    Zcbp_dotinv_ogf = unlabeled(plethystic_inverse(pointed(Zcbp_ci), n))
    Zcbp_comp_ogf = gf_pleth(Zcbp_ci, Zcbp_dotinv_ogf).add_bigoh(n+1)
    
    Znbp_prime_ogf = gf_pleth(Zcon(n), (x/Zcbp_dotinv_ogf - 1).add_bigoh(n+1)).add_bigoh(n) + 1
    
    return Zcbp_comp_ogf + x * Znbp_prime_ogf - x

print Znbp_ogf(nval)
