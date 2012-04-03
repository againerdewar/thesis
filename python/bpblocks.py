from sage.all import *
import sys

# Take arguments from the command line
args = sys.argv

assert len(args) == 2

nval = int(args[1])

##MATH BEGINS HERE
# Set up a ring of symmetric functions
p = SymmetricFunctionAlgebra(QQ, basis="power")
x = PowerSeriesRing(QQ, 'x').gen()

# Define basic objects
Zx = p[1]

Z2 = SymmetricGroup(2)
e = Z2.identity()
t = Z2.gen() #The non-identity element

# Utility function for composing a generating function into a cycle index
def gf_pleth(f, gf):
    partmapper = lambda part: prod(gf.subs({x:x^i}) for i in part)
    return p._apply_module_morphism(f, partmapper)

# Utility function for computing the ogf of unlabeled structures of a species with cycle index f
def unlabeled(f):
    partmapper = lambda part: x^(part.size())
    return p._apply_module_morphism(f, partmapper)

# Utility function for computing the egf of labeled structures of a species with cycle index f
def labeled(f):
    def partmapper(part):
        if part.length() == part.size():
            return x^(part.length())
        else:
            return 0
    return p._apply_module_morphism(f, partmapper)

# Compute a plethystic inverse of the symmetric function f to degree n
def plethystic_inverse(f, n):
        parent = f.parent()

        fstripped = f - f.restrict_degree(1, exact=True)

        improver = lambda F, i: Zx - fstripped.restrict_degree(i, exact=False).plethysm(F).restrict_degree(i, exact=False)

        finv = Zx

        for i in xrange(2, n+1):
            finv = improver(finv, i)

        return finv

# Utility function to compute the pointing of a cycle index
def pointed(f):
    return Zx*f.derivative_with_respect_to_p1()

# Compute the cycle index of the species E of sets
def Ze(n):
    return balanced_sum(1/part.aut() * prod(p[l] for l in part) for i in xrange(1,n+1) for part in Partitions(i))

# Compute the cycle index of the species Con which is the plethystic inverse of E
def Zcon(n):
    return plethystic_inverse(Ze(n), n)

# Utility function to compute the union of partitions
def union( mu, nu):
    return Partition(sorted(mu.to_list() + nu.to_list(), reverse=true))

# Utility function to compute the partwise multiple of a partition
def partmult( mu, n ):
    return Partition([part * n for part in mu.to_list()])

# Compute the number of bicolored graphs invariant under a permutation of cycle type mu acting on white vertices and a permutation of cycle type nu acting on black vertices
def efixedbcgraphs( mu, nu ):
    return 2^(sum([gcd(i, j) for i in mu for j in nu]))

# Compute the number of bicolored graphs for which a permutation of cycle type mu is a color-reversing isomorphism
def tfixedbcgraphs( mu ):
    return 2^(len(mu) + sum([integer_ceil(p/2) for p in mu]) + sum([gcd(mu[i], mu[j]) for i in range(0, len(mu)) for j in range(i+1, len(mu))]))

# Compute the Z2-cycle index of the species BC of bicolored graphs
def Zbc( z2elt, n ):
    assert z2elt in Z2
    if z2elt == Z2.identity():
        return add([efixedbcgraphs(pair[0], pair[1]) * p(union(pair[0],pair[1])) / (pair[0].aut() * pair[1].aut()) for i in range(1, n+1) for pair in PartitionTuples(i, 2).list()])
    else:
        return add([tfixedbcgraphs( mu ) * p(partmult(mu, 2))/partmult(mu, 2).aut() for i in range(1, integer_floor(n/2)+1) for mu in Partitions(i).list() ])

# Compute the Z2-cycle index of the species CBC of connected bicolored graphs
def Zcbc( z2elt, n ):
    assert z2elt in Z2
    if z2elt == Z2.identity():
        return Zcon(n).plethysm(Zbc(e, n)).restrict_degree(n, exact=False)
    else:
        scale_part = lambda n: lambda m: m.__class__([i*n for i in m])
        pn_pleth = lambda f, n: f.map_support(scale_part(n))
        f = lambda part: prod(pn_pleth(Zbc(t^i, n), i) for i in part)
        return p._apply_module_morphism(Zcon(n), f).restrict_degree(n, exact=False)

# Compute the cycle index of the species CBP of connected bipartite graphs
def Zcbp( n ):
    return 1/2 * (Zcbc(e, n) + Zcbc(t, n))

# Compute the ordinary generating function for nonseparable bipartite graphs
def Znbp_ogf( n ):
    Zcbp_ci = Zcbp(n)
    Zcbp_dotinv_ogf = unlabeled(plethystic_inverse(pointed(Zcbp_ci), n))
    Zcbp_comp_ogf = gf_pleth(Zcbp_ci, Zcbp_dotinv_ogf).add_bigoh(n+1)

    Znbp_prime_ogf = gf_pleth(Zcon(n), (x/Zcbp_dotinv_ogf - 1).add_bigoh(n+1)).add_bigoh(n) + 1

    return Zcbp_comp_ogf + x * Znbp_prime_ogf - x

# Print the result
print Znbp_ogf(nval)
