""" "Sum-product" representation of polynomial functors.
"""
module SumProdPolynomials
export AbstractSumProdPoly, SumProdPoly, modes, signatures,
  plus, times, otimes, ⊗, pairsum_mapout

using Catlab, Catlab.CategoricalAlgebra, Catlab.CategoricalAlgebra.FinSets
using ..FinPolynomials
import Catlab.Theories: plus, otimes, ⊗, compose

@present SumProdPolySchema(FreeSchema) begin
  (Mode, Out, Signature, In)::Ob
  mode::Hom(Signature, Mode)
  out_mode::Hom(Out, Mode)
  signature::Hom(In, Signature)

  Type::Data
  out_type::Attr(Out, Type)
  in_type::Attr(In, Type)
end

const AbstractSumProdPoly = AbstractACSetType(SumProdPolySchema)
const SumProdPoly = ACSetType(SumProdPolySchema,
                              index=[:mode,:out_mode,:signature])

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

function otimes(p::SumProdPoly{Symbol}, q::SumProdPoly{Symbol}) :: SumProdPoly{Symbol}

    r = SumProdPoly{Symbol}()
    comps = [:Mode, :Signature]
    pmodes, psigs = [nparts(p, x) for x in comps]
    qmodes, qsigs = [nparts(q, x) for x in comps]
    funs = [:out_mode, :signature]
    pmodefunc, psigfunc = [FinFunction(p, x) for x in funs]
    qmodefunc, qsigfunc = [FinFunction(q, x) for x in funs]

    sig_prod = product(FinSet(p, :Signature), FinSet(q, :Signature))
    sig1 = compose(proj1(sig_prod), FinFunction(p, :mode))
    sig2 = compose(proj2(sig_prod), FinFunction(q, :mode))
    sig_pair = pair(sig1, sig2)
    fs_out = Fibered_sum(pmodefunc, qmodefunc)
    fs_in  = Fibered_sum(psigfunc, qsigfunc)
    ot = pairsum_mapout(fs_out, p[:out_type], q[:out_type])
    it = pairsum_mapout(fs_in, p[:in_type], q[:in_type])
    add_parts!(r, :Mode, pmodes*qmodes)
    add_parts!(r, :Signature, psigs*qsigs, mode=collect(sig_pair))
    add_parts!(r, :Out, nparts(p, :Out)*qmodes + nparts(q, :Out)*pmodes,
               out_mode=collect(fs_out.h),
               out_type=ot)
    add_parts!(r, :In, nparts(p, :In)*qsigs + nparts(q, :In)*psigs,
               signature=collect(fs_in.h),
               in_type=it)
    return r

end

# function times(p::SumProdPoly{Symbol}, q::SumProdPoly{Symbol}) :: SumProdPoly{Symbol}

#     r = SumProdPoly{Symbol}()

#     pmodes = nparts(p, :Mode)
#     qmodes = nparts(q, :Mode)
#     pmodefunc = FinFunction(p[:out_mode], pmodes)
#     qmodefunc = FinFunction(q[:out_mode], qmodes)

#     psigs = nparts(p, :Signature)
#     qsigs = nparts(q, :Signature)
#     psigfunc = FinFunction(p[:signature], psigs)
#     qsigfunc = FinFunction(q[:signature], qsigs)

#     sig_prod = product(FinSet(psigs), FinSet(qsigs))
#     sig1 = compose(proj1(sig_prod), FinFunction(p[:mode], pmodes))
#     sig2 = compose(proj2(sig_prod), FinFunction(q[:mode], qmodes))
#     sig_pair = pair(sig1, sig2)

#     fs_sig = Fibered_sum(pmodefunc,qmodefunc)

#     add_parts!(r, :Mode, pmodes*qmodes)
#     add_parts!(r, :Signature, pmodes*qsigs + qmodes*psigs)

#     add_parts!(r, :Out, nparts(p, :Out)*qmodes + nparts(q, :Out)*pmodes)
#     add_parts!(r, :In, nparts(p, :In)*qsigs + nparts(q, :In)*psigs)

#     #fs_out = Fibered_sum(pmodefunc, qmodefunc)
#     fs_in  = Fibered_sum(psigfunc, qsigfunc)

#     set_subpart!(r, :mode, collect(fs_sig.h))
#     #set_subpart!(r, :out_mode, collect(fs_out.h))
#     set_subpart!(r, :signature, collect(fs_in.h))

#     #set_subpart!(r, :out_type, pairsum_mapout(Fibered_sum(pmodefunc, qmodefunc), p[:out_type], q[:out_type]))
#     set_subpart!(r, :in_type, pairsum_mapout(Fibered_sum(psigfunc, qsigfunc), p[:in_type], q[:in_type]))

#     return r

# end

function pairsum_mapout(ai_jb::Fibered_sum, at::Vector, bt::Vector)

    types = union(at,bt)
    at_index = FinFunction([findfirst(==(ty),types) for ty in at], length(types))
    bt_index = FinFunction([findfirst(==(ty),types) for ty in bt], length(types))

    mapout = copair(ai_jb.domain,
                  compose(ai_jb.p1, at_index),
                  compose(ai_jb.p2, bt_index))

    return types[collect(mapout)]

end



end
