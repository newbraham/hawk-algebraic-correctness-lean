import Hawk

/-!
## Statements being certified

The explicit statements below remain readable audit output. In addition, the
automatic audit checks every user-facing declaration in the `Hawk` namespace,
including private declarations after recovering their user names, against the
standard axiom list. Compiler-generated helpers whose names live outside
`Hawk` are excluded.
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

#check Hawk.Examples.modulus_three_counterexample
#print axioms Hawk.Examples.modulus_three_counterexample
