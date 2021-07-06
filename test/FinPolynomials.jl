module TestPoly
using Test

using Poly
using Catlab.CategoricalAlgebra: is_isomorphic

p = FinPoly([3,2,0])
@test p == FinPoly(FinFunction([1,1,1,2,2],3))
q = FinPoly([2,1])
@test p+q == FinPoly([3,2,0,2,1])
@test p * FinPoly([0]) == p
@test is_isomorphic(p * FinPoly([1]), FinPoly([4,3,1]))
@test is_isomorphic(p ⊗ FinPoly([1,2]), FinPoly([3,2,0,6,4,0]))

end
