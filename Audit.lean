import Hawk

/-!
## Statements being certified

The explicit statements below remain readable audit output. In addition, the
automatic audit checks every `Hawk` declaration selected by the filter below,
including private declarations after recovering their user names, against the
standard axiom list. Compiler-generated/internal helpers are excluded.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let rec hasInternalComponent : Name → Bool
    | .anonymous => false
    | .str p s => s.startsWith "_" || hasInternalComponent p
    | .num p _ => hasInternalComponent p
  let mut checked := 0
  for (name, _) in env.constants.toList do
    let userName := privateToUserName name
    if (`Hawk).isPrefixOf userName && !hasInternalComponent userName then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  if checked == 0 then
    throwError "No Hawk declarations found; the audit did not run"
  logInfo m!"Axiom audit passed for {checked} Hawk declarations. Allowed: {allowed}"

#check Hawk.CyclotomicTrace.geom_sum_eq_zero_of_pow_eq_one_of_ne_one
#print axioms Hawk.CyclotomicTrace.geom_sum_eq_zero_of_pow_eq_one_of_ne_one

#check Hawk.CyclotomicTrace.odd_power_sum_zero_of_primitive
#print axioms Hawk.CyclotomicTrace.odd_power_sum_zero_of_primitive

#check Hawk.CyclotomicTrace.normalized_trace_coeff_pairing
#print axioms Hawk.CyclotomicTrace.normalized_trace_coeff_pairing

#check Hawk.CyclotomicTrace.normalized_trace_coeff_inner
#print axioms Hawk.CyclotomicTrace.normalized_trace_coeff_inner

#check Hawk.CyclotomicTrace.normalized_trace_coeff_sq
#print axioms Hawk.CyclotomicTrace.normalized_trace_coeff_sq

#check Hawk.CyclotomicTrace.trace_pow_eq_zero_hawk
#print axioms Hawk.CyclotomicTrace.trace_pow_eq_zero_hawk

#check Hawk.CyclotomicTrace.traceOrthogonality_hawk
#print axioms Hawk.CyclotomicTrace.traceOrthogonality_hawk

#check Hawk.CyclotomicTrace.normalized_trace_coeff_pairing_hawk
#print axioms Hawk.CyclotomicTrace.normalized_trace_coeff_pairing_hawk

#check Hawk.CyclotomicTrace.cyclotomicConjugation_zeta
#print axioms Hawk.CyclotomicTrace.cyclotomicConjugation_zeta

#check Hawk.CyclotomicTrace.cyclotomic_trace_coeff_inner
#print axioms Hawk.CyclotomicTrace.cyclotomic_trace_coeff_inner

#check Hawk.CyclotomicTrace.cyclotomic_trace_coeff_sq
#print axioms Hawk.CyclotomicTrace.cyclotomic_trace_coeff_sq

#check Hawk.gram_identity
#print axioms Hawk.gram_identity

#check Hawk.signature_integral
#print axioms Hawk.signature_integral

#check Hawk.signature_integral_mod
#print axioms Hawk.signature_integral_mod

#check Hawk.flipped_signature_integral_iff
#print axioms Hawk.flipped_signature_integral_iff

#check Hawk.preimage_integral
#print axioms Hawk.preimage_integral

#check Hawk.exact_half_unique
#print axioms Hawk.exact_half_unique

#check Hawk.signing_correctness
#print axioms Hawk.signing_correctness

#check Hawk.signing_correctness_sign
#print axioms Hawk.signing_correctness_sign

#check Hawk.signing_correctness_mod
#print axioms Hawk.signing_correctness_mod

#check Hawk.signing_correctness_sign_mod
#print axioms Hawk.signing_correctness_sign_mod

#check Hawk.signing_correctness_over_ring
#print axioms Hawk.signing_correctness_over_ring

#check Hawk.verification_bound
#print axioms Hawk.verification_bound

#check Hawk.CyclotomicSigning.cyclotomicConjugation_involutive
#print axioms Hawk.CyclotomicSigning.cyclotomicConjugation_involutive

#check Hawk.CyclotomicSigning.cyclotomicTraceSq_coeffVector
#print axioms Hawk.CyclotomicSigning.cyclotomicTraceSq_coeffVector

#check Hawk.CyclotomicSigning.signing_correctness_coeff_norm
#print axioms Hawk.CyclotomicSigning.signing_correctness_coeff_norm

#check Hawk.CyclotomicSigning.hawk_rank2_algebraic_correctness
#print axioms Hawk.CyclotomicSigning.hawk_rank2_algebraic_correctness

#check Hawk.CyclotomicSigning.signing_correctness_sign_coeff_norm
#print axioms Hawk.CyclotomicSigning.signing_correctness_sign_coeff_norm

#check Hawk.CyclotomicSigning.signing_correctness_mod_coeff_norm
#print axioms Hawk.CyclotomicSigning.signing_correctness_mod_coeff_norm

#check Hawk.CyclotomicSigning.signing_correctness_sign_mod_coeff_norm
#print axioms Hawk.CyclotomicSigning.signing_correctness_sign_mod_coeff_norm

#check Hawk.Concrete.keyBasis
#print axioms Hawk.Concrete.keyBasis

#check Hawk.Concrete.coeffExpansion_coeffs
#print axioms Hawk.Concrete.coeffExpansion_coeffs

#check Hawk.Concrete.coeffs_coeffExpansion
#print axioms Hawk.Concrete.coeffs_coeffExpansion

#check Hawk.CyclotomicSigning.coeffSqQ_eq_zero_iff
#print axioms Hawk.CyclotomicSigning.coeffSqQ_eq_zero_iff

#check Hawk.CyclotomicSigning.coeffSqR_eq_zero_iff
#print axioms Hawk.CyclotomicSigning.coeffSqR_eq_zero_iff

#check Hawk.Geometry.traceSq_nonneg
#print axioms Hawk.Geometry.traceSq_nonneg

#check Hawk.Geometry.traceSq_eq_zero_iff
#print axioms Hawk.Geometry.traceSq_eq_zero_iff

#check Hawk.Geometry.publicSq_gram_nonneg
#print axioms Hawk.Geometry.publicSq_gram_nonneg

#check Hawk.Geometry.publicSq_gram_eq_zero_iff
#print axioms Hawk.Geometry.publicSq_gram_eq_zero_iff

#check Hawk.PublicKey.conjugation_mem_coeffRing
#print axioms Hawk.PublicKey.conjugation_mem_coeffRing

#check Hawk.PublicKey.gram_entries_integral
#print axioms Hawk.PublicKey.gram_entries_integral

#check Hawk.PublicKey.gram_hermitian
#print axioms Hawk.PublicKey.gram_hermitian

#check Hawk.PublicKey.keyMatrix_gram
#print axioms Hawk.PublicKey.keyMatrix_gram

#check Hawk.PublicKey.keyMatrix_gram_eq_zero_iff
#print axioms Hawk.PublicKey.keyMatrix_gram_eq_zero_iff

#check Hawk.IntegralCoefficients.integralPowerBasis_dim
#print axioms Hawk.IntegralCoefficients.integralPowerBasis_dim

#check Hawk.IntegralCoefficients.integralHawkBasis_apply
#print axioms Hawk.IntegralCoefficients.integralHawkBasis_apply

#check Hawk.IntegralCoefficients.integer_coeffExpansion
#print axioms Hawk.IntegralCoefficients.integer_coeffExpansion

#check Hawk.IntegralCoefficients.coeffs_integral
#print axioms Hawk.IntegralCoefficients.coeffs_integral

#check Hawk.IntegralCoefficients.mem_coeffRing_iff_coeffs_integral
#print axioms Hawk.IntegralCoefficients.mem_coeffRing_iff_coeffs_integral

#check Hawk.PolynomialQuotient.cyclotomic_hawk_eq
#print axioms Hawk.PolynomialQuotient.cyclotomic_hawk_eq

#check Hawk.PolynomialQuotient.minpoly_hawkZeta
#print axioms Hawk.PolynomialQuotient.minpoly_hawkZeta

#check Hawk.PolynomialQuotient.adjoinRootEquiv
#print axioms Hawk.PolynomialQuotient.adjoinRootEquiv

#check Hawk.PolynomialQuotient.quotientRingEquiv
#print axioms Hawk.PolynomialQuotient.quotientRingEquiv

#check Hawk.Concrete.coeffVector_vectorCoeffs
#print axioms Hawk.Concrete.coeffVector_vectorCoeffs

#check Hawk.Concrete.cosetPoint_in_coset
#print axioms Hawk.Concrete.cosetPoint_in_coset

#check Hawk.Concrete.signing_correctness_mod_coeff_norm_auto
#print axioms Hawk.Concrete.signing_correctness_mod_coeff_norm_auto

#check Hawk.Concrete.hawk_rank2_algebraic_interface
#print axioms Hawk.Concrete.hawk_rank2_algebraic_interface

#check Hawk.Functional.symBreak_canonicalW
#print axioms Hawk.Functional.symBreak_canonicalW

#check Hawk.Functional.decompress_compress_of_rebuild
#print axioms Hawk.Functional.decompress_compress_of_rebuild

#check Hawk.Functional.canonicalSignature_integral
#print axioms Hawk.Functional.canonicalSignature_integral

#check Hawk.Functional.reconstruction_canonicalSignature
#print axioms Hawk.Functional.reconstruction_canonicalSignature

#check Hawk.Functional.canonicalSignature_symBreak
#print axioms Hawk.Functional.canonicalSignature_symBreak

#check Hawk.Functional.canonicalSignature_publicSq
#print axioms Hawk.Functional.canonicalSignature_publicSq

#check Hawk.Functional.PostHashChecks
#print axioms Hawk.Functional.PostHashChecks

#check Hawk.Functional.postHashChecks_compress
#print axioms Hawk.Functional.postHashChecks_compress

#check Hawk.Functional.hawk_rank2_conditional_postHash_acceptance
#print axioms Hawk.Functional.hawk_rank2_conditional_postHash_acceptance

#check Hawk.Examples.modulus_three_counterexample
#print axioms Hawk.Examples.modulus_three_counterexample
