""" "Sum-product" representation of polynomial functors.
"""
module SumProdPolynomials
export AbstractSumProdPoly, SumProdPoly, modes, signatures,
  plus, times, otimes, ⊗, pairsum_mapout

using Catlab, Catlab.CategoricalAlgebra, Catlab.CategoricalAlgebra.FinSets
using ..FinPolynomials
import Catlab.Theories: plus, otimes, ⊗, compose, id
import Catlab.CategoricalAlgebra.Limits: coproduct, product


"""
Polynomials of the form:

Σₘ (Πₒ (Tₒ ⋅ y ^( Σₛ Πᵢ Tᵢ )))
  where:
    m ∈ Mode
    o ∈ out_mode⁻¹(m)
    s ∈ mode⁻¹(m)
    i ∈ signature⁻¹(s)
    Tₒ = out_type(o)
    Tᵢ = in_type(i)

Out ⟶ Mode ⟵ Signature ⟵ In
 ↓                          ↓
Type == == == == == == == Type
"""
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

function product(p::FinFunction, q::FinFunction)
  dom_prod = product(dom(p), dom(q))
  f1 = compose(proj1(dom_prod), p)
  f2 = compose(proj2(dom_prod), q)
  return pair(f1, f2)
end

function coproduct(p::FinFunction, q::FinFunction)
  codom_coprod = coproduct(codom(p), codom(q))
  f1 = compose(p, coproj1(codom_coprod))
  f2 = compose(q, coproj2(codom_coprod))
  return copair(coproduct(dom(p),dom(q)), f1, f2)
end

"""
O₁M₂+M₁O₂ ⟶ M₁M₂ ⟵ S₁S₂ ⟵ I₁S₂+S₁I₂
 ↓                               ↓
Type == == == == == == == == == Type
"""
function otimes(p::SumProdPoly{Symbol}, q::SumProdPoly{Symbol})::SumProdPoly{Symbol}
    r = SumProdPoly{Symbol}()
    comps = [:Mode, :Signature]
    pmodes, psigs = [nparts(p, x) for x in comps]
    qmodes, qsigs = [nparts(q, x) for x in comps]
    funs = [:out_mode, :signature]
    pmodefunc, psigfunc = [FinFunction(p, x) for x in funs]
    qmodefunc, qsigfunc = [FinFunction(q, x) for x in funs]

    sig_pair = product(FinFunction(p, :mode), FinFunction(q, :mode))
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

"""
O₁M₂+M₁O₂ ⟶ M₁M₂ ⟵ S₁M₂+M₁S₂ ⟵ I₁M₂+M₁I₂
 ↓                                    ↓
Type == == == == == == == == == == == Type
"""
function times(p::SumProdPoly{Symbol}, q::SumProdPoly{Symbol}) :: SumProdPoly{Symbol}

    r = SumProdPoly{Symbol}()

    comps = [:Mode, :Signature]
    pmodes, psigs = [nparts(p, x) for x in comps]
    qmodes, qsigs = [nparts(q, x) for x in comps]
    funs = [:out_mode, :signature, :mode]
    poutmodefunc, psigfunc, psigmodefunc = [FinFunction(p, x) for x in funs]
    qoutmodefunc, qsigfunc, qsigmodefunc = [FinFunction(q, x) for x in funs]

    fs_sig = Fibered_sum(psigmodefunc, qsigmodefunc)
    fs_out = Fibered_sum(poutmodefunc, qoutmodefunc)
    fs_in  = Fibered_sum(compose(psigfunc, psigmodefunc), compose(qsigfunc, qsigmodefunc))
    ot = pairsum_mapout(fs_out, p[:out_type], q[:out_type])
    it = pairsum_mapout(fs_in, p[:in_type], q[:in_type])

    
    sig1 = product(FinFunction(p, :signature), id(FinSet(q, :Mode)))
    sig2 = product(id(FinSet(p, :Mode)), FinFunction(q, :signature))

    println("sig1 $sig1\n sig2 $sig2")
    sig = coproduct(sig1, sig2)
    println("sig1+sig2 $sig $(collect(sig))")
    add_parts!(r, :Mode, pmodes*qmodes)
    add_parts!(r, :Signature, pmodes*qsigs + qmodes*psigs,
               mode=collect(fs_sig.h))

    add_parts!(r, :Out, nparts(p, :Out)*qmodes + nparts(q, :Out)*pmodes,
               out_mode = collect(fs_out.h), out_type=ot)
    println("sig1+sig2 $sig $(collect(sig))\n $(nparts(p, :In)*qmodes + nparts(q, :In)*pmodes)")
    add_parts!(r, :In, nparts(p, :In)*qmodes + nparts(q, :In)*pmodes,
              signature=collect(sig), in_type=it) # BUG IN sig , 
    # 

    return r

end

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
