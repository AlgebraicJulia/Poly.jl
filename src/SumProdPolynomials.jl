""" "Sum-product" representation of polynomial functors.
"""
module SumProdPolynomials
export AbstractSumProdPoly, SumProdPoly, modes, signatures

using Catlab, Catlab.CategoricalAlgebra, Catlab.CategoricalAlgebra.FinSets

@present SumProdPolySchema(FreeSchema) begin
  (Mode, Out, Signature, In)::Ob
  mode::Hom(Signature, Mode)
  out_mode::Hom(Out, Mode)
  in_signature::Hom(In, Signature)

  Type::Data
  out_type::Attr(Out, Type)
  in_type::Attr(In, Type)
end

const AbstractSumProdPoly = AbstractACSetType(SumProdPolySchema)
const SumProdPoly = ACSetType(SumProdPolySchema,
                              index=[:mode,:in_mode,:in_signature])

modes(p::AbstractSumProdPoly) = FinSet(p, :Mode)
signatures(p::AbstractSumProdPoly) = FinSet(p, :Signature)
signatures(p::AbstractSumProdPoly, mode) = incident(p, :mode, mode)

end
