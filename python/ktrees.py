from sage.all import *
import sys

# Take arguments from the command line
args = sys.argv

assert len(args) == 3

kval = int(args[1])
nval = int(args[2])

# Set up a ring of formal power series
psr = PowerSeriesRing(QQ, 'x')
x = psr.gen()

# The permutation-rotating map rho
@cached_function
def rho(sigma, i):
    pgroup = sigma.parent()
    deg = pgroup.degree()
    shiftmod = lambda k: mod(k-1, deg).lift() + 1
    result_list = [shiftmod( sigma(shiftmod(i+a)) - sigma(shiftmod(i)) ) for a in xrange(1, deg)]
    return SymmetricGroup(deg-1)(result_list)

# The dimension-lifting map Delta
def Delta(sigma):
    deg = sigma.parent().degree()
    outgroup = SymmetricGroup(deg+1)
    return outgroup(sigma)

# Permutation.cycle_tuples() doesn't include 1-cycles, but we need them for cycle index calculations, so we define a new map
@cached_function
def perm_cycles(sigma):
        cycles = sigma.cycle_tuples()

        # find fixed-points of sigma (which are missing from cycle_tuples)
        biggest_number = sigma.parent().degree()
        values = set(range(1, biggest_number + 1))

        usedvalues = set([i for cyc in sigma.cycle_tuples() for i in cyc])

        values -= usedvalues

        # add fixed-points as 1-cycles
        cycles += [(i,) for i in values]
        return cycles

# Compute the generating function for unlabeled Y-rooted k-trees fixed by a given sigma.
# Note that sigma should be in S(k)
@cached_function
def unlY(sigma, n):
    pgroup = sigma.parent()
    assert pgroup in FinitePermutationGroups(), "%s is not a permutation!" %(sigma)

    if n <= 0:
        return psr(1)
    else:
        def permconst(cyc, perm):
            return prod(rho(Delta(perm), i) for i in cyc)

        def ystretcher(cyc, perm):
            return unlY(permconst(cyc, perm), floor((n-1)/len(cyc))).subs({x:x**len(cyc)})

        def descendant_pseries(perm):
            return prod(ystretcher(cyc, perm) for cyc in perm_cycles(perm))

        return sum(x**i/i * descendant_pseries(sigma**i).subs({x:x**i}) for i in xrange(1, n+1)).exp(n+1)

# Compute the generating function for unlabeled XY-rooted k-trees fixed by a given sigma.
# Note that sigma should be in S(k+1)
@cached_function
def unlXY(sigma, n):
    pgroup = sigma.parent()
    assert pgroup in FinitePermutationGroups(), "%s is not a permutation!" %(sigma)

    if n <= 0:
        return psr(0)
    else:
        def permconst(cyc):
            return prod(rho(sigma, i) for i in cyc)

        def ystretcher(cyc):
            return unlY(permconst(cyc), floor((n-1)/len(cyc))).subs({x:x**len(cyc)})

        cycles = perm_cycles(sigma)
        return (x * prod(ystretcher(c) for c in cycles)).add_bigoh(n+1)

# Compute the generating functions for unlabeled X-, Y-, and XY-rooted k-trees using quotients
ax = lambda k, n: 1/factorial(k+1) * sum(unlXY(sigma, n) for sigma in SymmetricGroup(k+1))
ay = lambda k, n: 1/factorial(k) * sum(unlY(sigma, n) for sigma in SymmetricGroup(k))
axy = lambda k, n: 1/factorial(k) * sum(unlXY(Delta(sigma), n) for sigma in SymmetricGroup(k))

# Compute the generating function for unlabeled un-rooted k-trees using the dissymmetry theorem
a = lambda k, n: ax(k, n) + ay(k, n) - axy(k, n)

# Print the result
print a(kval, nval)
