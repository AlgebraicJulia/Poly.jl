module Poly
export AbstractFinPolynomial, FinPolynomial, FinSet, FinFunction,
  positions, directions, proj, plus, times, otimes, ⊗,
  AbstractPolynomial, Polynomial, modes, signatures

using Catlab, Catlab.CategoricalAlgebra, Catlab.CategoricalAlgebra.FinSets
using Catlab.Theories
import Catlab.Theories: proj, plus, times, otimes, ⊗

# Finite polynomials
####################

@present FinPolynomialSchema(FreeSchema) begin
  (Pos, Dir)::Ob
  pos::Hom(Dir, Pos)
end

""" Abstract type for finite polynomial functors. See [`FinPolynomial`](@ref).
"""
const AbstractFinPolynomial = AbstractACSetType(FinPolynomialSchema)

""" Finite polynomial functor, i.e., polynomial endofunctor on FinSet.

A finite polynomial is a polynomial whose sets of positions and directions are
finite. These are simple but perhaps not very useful on their own. For a richer
class of polynomials, see [`Polynomial`](@ref).

Finite polynomials can be constructed from a list of exponents or from the
position-direction projection. For example, both `FinPolynomial([3,2,0])` and
`FinPolynomial(FinFunction([1,1,1,2,2],3))` yield the polynomial ``y³+y²+1``.
"""
const FinPolynomial = ACSetType(FinPolynomialSchema, index=[:pos])

function (::Type{P})(ndirs::AbstractVector{Int}) where P <: AbstractFinPolynomial
  p = P()
  add_parts!(p, :Pos, length(ndirs))
  for (pos, ndir) in enumerate(ndirs)
    add_parts!(p, :Dir, ndir, pos=pos)
  end
  p
end

function (::Type{P})(f::FinFunction) where P <: AbstractFinPolynomial
  p = P()
  add_parts!(p, :Pos, length(codom(f)))
  add_parts!(p, :Dir, length(dom(f)), pos=collect(f))
  p
end

""" Positions of a polynomial.
"""
positions(p::AbstractFinPolynomial) = FinSet(p, :Pos)

""" All directions of a polynomial, or directions at a given position.
"""
directions(p::AbstractFinPolynomial) = FinSet(p, :Dir)
directions(p::AbstractFinPolynomial, pos) = incident(p, :pos, pos)

""" Projection from directions to positions in a polynomial.
"""
proj(p::AbstractFinPolynomial) = FinFunction(p, :pos)

plus(p::AbstractFinPolynomial, q::AbstractFinPolynomial) = ob(coproduct(p, q))
Base.:+(p::AbstractFinPolynomial, q::AbstractFinPolynomial) = plus(p, q)

times(p::P, q::P) where P <: AbstractFinPolynomial =
  P(fiber_sum(proj(p), proj(q)))
Base.:*(p::AbstractFinPolynomial, q::AbstractFinPolynomial) = times(p, q)

otimes(p::AbstractFinPolynomial, q::AbstractFinPolynomial) = ob(product(p, q))
⊗(p, q) = otimes(p, q)

# Sum-of-product polynomials
############################

@present PolynomialSchema(FreeSchema) begin
  (Mode, Out, Signature, In)::Ob
  mode::Hom(Signature, Mode)
  out_mode::Hom(Out, Mode)
  in_signature::Hom(In, Signature)

  Type::Data
  out_type::Attr(Out, Type)
  in_type::Attr(In, Type)
end

const AbstractPolynomial = AbstractACSetType(PolynomialSchema)
const Polynomial = ACSetType(PolynomialSchema,
                             index=[:mode,:in_mode,:in_signature])

modes(p::AbstractPolynomial) = parts(p, :Mode)
signatures(p::AbstractPolynomial) = parts(p, :Signature)
signatures(p::AbstractPolynomial, mode) = incident(p, :mode, mode)

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
