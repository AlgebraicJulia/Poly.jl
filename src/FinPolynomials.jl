"""
A *finite polynomial* is a polynomial endofunctor on FinSet or equivalently a
polynomial functor whose sets of positions and directions are finite. These
objects are simple but perhaps not very useful on their own. For a richer class
of polynomials, see the module [`SumProdPolynomials`](@ref).
"""
module FinPolynomials
export AbstractFinPoly, FinPoly, FinSet, FinFunction, positions, directions,
  proj, plus, times, otimes, ⊗

using Catlab, Catlab.CategoricalAlgebra, Catlab.CategoricalAlgebra.FinSets
using Catlab.Theories
import Catlab.Theories: proj, plus, otimes, ⊗

@present FinPolySchema(FreeSchema) begin
  (Pos, Dir)::Ob
  pos::Hom(Dir, Pos)
end

""" Abstract type for finite polynomial. See [`FinPolynomial`](@ref).
"""
@abstract_acset_type AbstractFinPoly

""" Finite polynomial, i.e., polynomial endofunctor on FinSet.

Finite polynomials can be constructed from a list of exponents or from the
position-direction projection. For example, both `FinPoly([3,2,0])` and
`FinPoly(FinFunction([1,1,1,2,2],3))` yield the polynomial ``y³+y²+1``.
"""
@acset_type FinPoly(FinPolySchema, index=[:pos]) <: AbstractFinPoly

function (::Type{P})(ndirs::AbstractVector{Int}) where P <: AbstractFinPoly
  p = P()
  add_parts!(p, :Pos, length(ndirs))
  for (pos, ndir) in enumerate(ndirs)
    add_parts!(p, :Dir, ndir, pos=pos)
  end
  p
end

function (::Type{P})(f::FinFunction) where P <: AbstractFinPoly
  p = P()
  add_parts!(p, :Pos, length(codom(f)))
  add_parts!(p, :Dir, length(dom(f)), pos=collect(f))
  p
end

""" Positions of a polynomial.
"""
positions(p::AbstractFinPoly) = FinSet(p, :Pos)

""" All directions of a polynomial, or directions at a given position.
"""
directions(p::AbstractFinPoly) = FinSet(p, :Dir)
directions(p::AbstractFinPoly, pos) = incident(p, pos, :pos)

""" Projection from directions to positions in a polynomial.
"""
proj(p::AbstractFinPoly) = FinFunction(p, :pos)

plus(p::AbstractFinPoly, q::AbstractFinPoly) = ob(coproduct(p, q))
Base.:+(p::AbstractFinPoly, q::AbstractFinPoly) = plus(p, q)

times(p::P, q::P) where P <: AbstractFinPoly = P(fiber_sum(proj(p), proj(q)))
Base.:*(p::AbstractFinPoly, q::AbstractFinPoly) = times(p, q)

otimes(p::AbstractFinPoly, q::AbstractFinPoly) = ob(product(p, q))
⊗(p, q) = otimes(p, q)

# Set constructions
###################

""" Fiber sum of indexed sets.

Given indexed sets ``Xᵢ``, ``i ∈ I``, and ``Yⱼ``, ``j ∈ J``, represented by
functions ``f: X → I`` and ``g: Y → J``, compute the "fiber sum" ``Xᵢ+Yⱼ``,
``(i,j) ∈ I×J``, as a function ``X×J + I×Y → I×J``.
"""
function fiber_sum(f, g)
  X, Y, I, J = dom(f), dom(g), codom(f), codom(g)
  XJ, IY, IJ = product(X,J), product(I,Y), product(I,J)
  fJ = pair(IJ, proj1(XJ)⋅f, proj2(XJ)) # f×id(J) : X×J → I×J
  Ig = pair(IJ, proj1(IY), proj2(IY)⋅g) # id(I)×g : I×Y → I×J
  copair(coproduct(ob(XJ), ob(IY)), fJ, Ig)
end

end
