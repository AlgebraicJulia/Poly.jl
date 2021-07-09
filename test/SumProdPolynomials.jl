module TestSumProdPolynomials
export p,q,r,pr,pr_expected,pq,pq_expected

using Test
using Poly
using Catlab.CategoricalAlgebra.CSets


# SA⋅y^S + S⋅y^B
p = SumProdPoly{Symbol}([ [[:B]] => [:S], [[:S]] => [:S,:A] ])
q = SumProdPoly{Symbol}([ [[:A]] => [:B] ])
# y + A⋅y^(BS)
r = SumProdPoly{Symbol}([ [[:B],[:S]] => [:A] , [[]] => [] ])

@test p+q == SumProdPoly{Symbol}([
 [[:B]] => [:S], [[:S]] => [:S,:A], [[:A]] => [:B],
])

# Expected
pr_x = SumProdPoly{Symbol}([
           [[:B,:B],[:B,:S]] => [:A,:S],
           [[:B,:S], [:S,:S]] => [:S,:A,:A],
           [[:B]] => [:S],
           [[:S]] => [:S,:A]])

pr = otimes(p,r)

@test is_isomorphic(pr,pr_x)

p_times_r_x = SumProdPoly{Symbol}([ # Expected
            [[:B],[:B],[:S]] => [:A,:S],
            [[:S],[:B],[:S]] => [:S,:A,:A],
            [[:B],[]] => [:S],
            [[:S],[]] => [:S,:A]])

p_times_r = times(p,r)

@test is_isomorphic(p_times_r, p_times_r_x)

end
