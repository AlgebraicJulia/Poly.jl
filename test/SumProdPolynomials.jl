module TestSumProdPolynomials
using Test

using Poly
using Catlab.CategoricalAlgebra.CSets

p = SumProdPoly{Symbol}([ [[:B]] => [:S], [[:S]] => [:S,:A] ])
q = SumProdPoly{Symbol}([ [[:A]] => [:B] ])
r = SumProdPoly{Symbol}([ [[:B],[:S]] => [:A] , [[]] => [] ])

#@test p+q == SumProdPoly{Symbol}([
#  [[:B]] => [:S], [[:S]] => [:S,:A], [[:A]] => [:B],
#])

#pr = otimes(p,r)
#pr_expected =
#    SumProdPoly{Symbol}([
#            [[:B,:B],[:B,:S]] => [:A,:S],
#            [[:B,:S], [:S,:S]] => [:S,:A,:A],
#            [[:B]] => [:S],
#            [[:S]] => [:S,:A]
#    ])
#@test is_isomorphic(pr,pr_expected)
#

pq = times(p,q)
pq_expected = SumProdPoly{Symbol}([
            [[:B],[:B],[:S]] => [:A,:S],
            [[:S],[:B],[:S]] => [:S,:A,:A],
            [[:B],[]] => [:S],
            [[:S],[]] => [:S,:A]
])

print(pq)

#@test is_isomorphic(pq, pq_expected)

end
