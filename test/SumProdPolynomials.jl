module TestSumProdPolynomials
using Test

using Poly

p = SumProdPoly{Symbol}([ [[:B]] => [:S], [[:S]] => [:S,:A] ])
q = SumProdPoly{Symbol}([ [[:A]] => [:B] ])
@test p+q == SumProdPoly{Symbol}([
  [[:B]] => [:S], [[:S]] => [:S,:A], [[:A]] => [:B],
])

end
