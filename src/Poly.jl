module Poly

using Reexport

include("FinPolynomials.jl")
include("SumProdPolynomials.jl")

@reexport using .FinPolynomials
@reexport using .SumProdPolynomials

end
