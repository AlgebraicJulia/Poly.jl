""" "Sum-product" representation of polynomial functors.
"""
module SumProdPolynomials
export AbstractSumProdPoly, SumProdPoly, modes, signatures,
  plus, times, otimes, ⊗

using Catlab, Catlab.CategoricalAlgebra, Catlab.CategoricalAlgebra.FinSets
import Catlab.Theories: plus, otimes, ⊗

@present SumProdPolySchema(FreeSchema) begin
  (Mode, Out, Signature, In)::Ob
  mode::Hom(Signature, Mode)
  out_mode::Hom(Out, Mode)
  signature::Hom(In, Signature)

  Type::AttrType
  out_type::Attr(Out, Type)
  in_type::Attr(In, Type)
end

@abstract_acset_type AbstractSumProdPoly
@acset_type SumProdPoly(SumProdPolySchema,
                        index=[:mode,:out_mode,:signature]) <: AbstractSumProdPoly

function (::Type{P})(modes::AbstractVector) where P <: AbstractSumProdPoly
  p = P()
  for (input_signatures, outputs) in modes
    add_mode!(p, input_signatures, outputs)
  end
  p
end

modes(p::AbstractSumProdPoly) = FinSet(p, :Mode)
signatures(p::AbstractSumProdPoly) = FinSet(p, :Signature)
signatures(p::AbstractSumProdPoly, mode) = incident(p, :mode, mode)

function add_mode!(p::AbstractSumProdPoly, input_signatures, outputs)
  mode = add_part!(p, :Mode)
  add_parts!(p, :Out, length(outputs), out_mode=mode, out_type=outputs)

  sigs = add_parts!(p, :Signature, length(input_signatures), mode=mode)
  for (sig, inputs) in zip(sigs, input_signatures)
    add_parts!(p, :In, length(inputs), signature=sig, in_type=inputs)
  end
end

plus(p::AbstractSumProdPoly, q::AbstractSumProdPoly) = ob(coproduct(p, q))
Base.:+(p::AbstractSumProdPoly, q::AbstractSumProdPoly) = plus(p, q)

end
