module TestPoly
using Test

using Poly
using Catlab.CategoricalAlgebra: is_isomorphic

p = FinPolynomial([3,2,0])
@test p == FinPolynomial(FinFunction([1,1,1,2,2],3))
q = FinPolynomial([2,1])
@test p+q == FinPolynomial([3,2,0,2,1])
@test p * FinPolynomial([0]) == p
@test is_isomorphic(p * FinPolynomial([1]), FinPolynomial([4,3,1]))
@test is_isomorphic(p ⊗ FinPolynomial([1,2]), FinPolynomial([3,2,0,6,4,0]))

end
