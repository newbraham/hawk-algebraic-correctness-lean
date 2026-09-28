import Mathlib.Algebra.Star.Module
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Cyclotomic trace and the coefficient inner product

This file formalizes the cyclotomic trace calculation used by the HAWK case study in two layers.

The first layer contains reusable algebraic lemmas: the finite geometric-series
calculation and the implication from trace orthogonality to the coefficient dot
product.

The second layer discharges the trace-orthogonality interface from Mathlib's
actual cyclotomic-extension theory.  For the power-of-two HAWK field, with

* `n = 2^k`,
* conductor `2n`,
* `ζ` a primitive `(2n)`-th root,

it proves that the embeddings are enumerated by the odd powers
`ζ ↦ ζ^(2t+1)`, computes the field trace of every nontrivial power
`ζ^j`, `0 < j < n`, and derives

`(1/n) Tr(a^* b) = ∑ i, a_i b_i`.

The final theorems use the concrete cyclotomic automorphism sending the
canonical primitive root `ζ` to `ζ⁻¹`; no project axiom or
`TraceOrthogonality` hypothesis is left in their statements.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Hawk.CyclotomicTrace

/-! ## The geometric-series calculation -/

/-- A geometric sum vanishes when its ratio is a nontrivial `n`-th root of one. -/
theorem geom_sum_eq_zero_of_pow_eq_one_of_ne_one
    {F : Type*} [Field F] (r : F) (n : ℕ)
    (hrn : r ^ n = 1) (hr : r ≠ 1) :
    ∑ t ∈ Finset.range n, r ^ t = 0 := by
  have hprod :
      (∑ t ∈ Finset.range n, r ^ t) * (r - 1) = 0 := by
    simpa [hrn] using (geom_sum_mul r n)
  exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hr)

/--
The finite geometric-series step used in the cyclotomic trace calculation. If `ζ` is
primitive of order `2n` and `0 < j < n`, then

`∑_{t=0}^{n-1} ζ^((2t+1)j) = 0`.
-/
theorem odd_power_sum_zero_of_primitive
    {F : Type*} [Field F] {ζ : F} {n j : ℕ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) (hj0 : 0 < j) (hjn : j < n) :
    ∑ t ∈ Finset.range n, ζ ^ ((2 * t + 1) * j) = 0 := by
  have hratio_ne : ζ ^ (2 * j) ≠ 1 := by
    intro h
    have hdvd : 2 * n ∣ 2 * j := hζ.dvd_of_pow_eq_one (2 * j) h
    have hnj : n ∣ j :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) hdvd
    exact (Nat.not_dvd_of_pos_of_lt hj0 hjn) hnj
  have hratio_pow : (ζ ^ (2 * j)) ^ n = 1 := by
    calc
      (ζ ^ (2 * j)) ^ n = ζ ^ ((2 * j) * n) := by rw [← pow_mul]
      _ = ζ ^ ((2 * n) * j) := by
        congr 1
        ac_rfl
      _ = (ζ ^ (2 * n)) ^ j := by rw [pow_mul]
      _ = 1 := by rw [hζ.pow_eq_one, one_pow]
  have hgeom :=
    geom_sum_eq_zero_of_pow_eq_one_of_ne_one (ζ ^ (2 * j)) n hratio_pow hratio_ne
  calc
    (∑ t ∈ Finset.range n, ζ ^ ((2 * t + 1) * j)) =
        ζ ^ j * ∑ t ∈ Finset.range n, (ζ ^ (2 * j)) ^ t := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          calc
            ζ ^ ((2 * t + 1) * j) = ζ ^ (j + (2 * j) * t) := by
              congr 1
              ring
            _ = ζ ^ j * ζ ^ ((2 * j) * t) := by rw [pow_add]
            _ = ζ ^ j * (ζ ^ (2 * j)) ^ t := by rw [pow_mul]
    _ = 0 := by rw [hgeom, mul_zero]

/-! ## Generic coefficient-pairing layer -/

section TracePairing

variable {E : Type*} [Field E] [Algebra ℚ E]
variable {n : ℕ}

/-- The coefficient expansion `∑ a_i ζ^i`. -/
def coeffExpansion (ζ : E) (a : Fin n → ℚ) : E :=
  ∑ i, a i • ζ ^ (i : ℕ)

/-- The expansion obtained by replacing `ζ` with `ζ⁻¹`. -/
def coeffConjExpansion (ζ : E) (a : Fin n → ℚ) : E :=
  ∑ i, a i • (ζ⁻¹) ^ (i : ℕ)

/-- The field trace divided by `n`, packaged as a `ℚ`-linear map. -/
def normalizedTraceQ (n : ℕ) : E →ₗ[ℚ] ℚ :=
  (n : ℚ)⁻¹ • Algebra.trace ℚ E

/--
The exact orthogonality statement needed from the power-of-two cyclotomic
setting.  The end-to-end part below proves this predicate rather than assuming
it.
-/
def TraceOrthogonality (ζ : E) : Prop :=
  ∀ i j : Fin n,
    normalizedTraceQ (E := E) n (((ζ⁻¹) ^ (i : ℕ)) * ζ ^ (j : ℕ)) =
      if i = j then 1 else 0

/-- Linear combinations inherit the coefficient dot product from trace orthogonality. -/
theorem normalized_trace_coeff_pairing
    (ζ : E) (horth : TraceOrthogonality (E := E) (n := n) ζ)
    (a b : Fin n → ℚ) :
    normalizedTraceQ (E := E) n
        (coeffConjExpansion ζ a * coeffExpansion ζ b) =
      ∑ i, a i * b i := by
  unfold coeffConjExpansion coeffExpansion
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [map_sum]
  simp only [smul_mul_smul, map_smul, smul_eq_mul]
  unfold TraceOrthogonality at horth
  simp_rw [horth]
  simp

section Star

variable [StarRing E]

/-- If star sends `ζ` to `ζ⁻¹`, it acts on coefficient expansions as expected. -/
theorem star_coeffExpansion
    (ζ : E) (hstar : star ζ = ζ⁻¹) (a : Fin n → ℚ) :
    star (coeffExpansion ζ a) = coeffConjExpansion ζ a := by
  simp [coeffExpansion, coeffConjExpansion, hstar]

/-- Generic consequence: normalized trace equals the coefficient inner product. -/
theorem normalized_trace_coeff_inner
    (ζ : E) (hstar : star ζ = ζ⁻¹)
    (horth : TraceOrthogonality (E := E) (n := n) ζ)
    (a b : Fin n → ℚ) :
    normalizedTraceQ (E := E) n
        (star (coeffExpansion ζ a) * coeffExpansion ζ b) =
      ∑ i, a i * b i := by
  rw [star_coeffExpansion ζ hstar a]
  exact normalized_trace_coeff_pairing ζ horth a b

/-- Generic squared-norm specialization. -/
theorem normalized_trace_coeff_sq
    (ζ : E) (hstar : star ζ = ζ⁻¹)
    (horth : TraceOrthogonality (E := E) (n := n) ζ)
    (a : Fin n → ℚ) :
    normalizedTraceQ (E := E) n
        (star (coeffExpansion ζ a) * coeffExpansion ζ a) =
      ∑ i, (a i) ^ 2 := by
  simpa [pow_two] using normalized_trace_coeff_inner ζ hstar horth a a

end Star
end TracePairing

/-! ## Power-of-two cyclotomic specialization -/

/-- The HAWK field degree `n = 2^k`. -/
def hawkDegree (k : ℕ) : ℕ := 2 ^ k

/-- The HAWK cyclotomic conductor `2n`. -/
def hawkConductor (k : ℕ) : ℕ+ :=
  ⟨2 * hawkDegree k, Nat.mul_pos (by norm_num) (pow_pos (by norm_num) k)⟩

@[simp]
theorem hawkDegree_pos (k : ℕ) : 0 < hawkDegree k := by
  exact pow_pos (by norm_num) k

@[simp]
theorem hawkConductor_coe (k : ℕ) :
    (hawkConductor k : ℕ) = 2 * hawkDegree k := rfl

/-- Euler's totient of the power-of-two conductor is exactly the HAWK degree. -/
theorem totient_hawkConductor (k : ℕ) :
    Nat.totient (hawkConductor k : ℕ) = hawkDegree k := by
  simpa [hawkConductor, hawkDegree, pow_succ, Nat.mul_comm] using
    (Nat.totient_prime_pow_succ Nat.prime_two k)

section OddEmbeddings

variable {C : Type*} [Field C]

/-- The `t`-th odd power of a primitive `(2n)`-th root, as a primitive root. -/
def oddPrimitiveRoot (k : ℕ) (ξ : C)
    (hξ : IsPrimitiveRoot ξ (hawkConductor k))
    (t : Fin (hawkDegree k)) :
    ↥(primitiveRoots (hawkConductor k) C) := by
  refine ⟨ξ ^ (2 * (t : ℕ) + 1), ?_⟩
  apply (mem_primitiveRoots (hawkConductor k).2).2
  apply hξ.pow_of_coprime
  have hc : Nat.Coprime (2 * (t : ℕ) + 1) (2 ^ (k + 1)) := by
    rw [Nat.coprime_pow_right_iff (by omega : 0 < k + 1)]
    rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
    exact (odd_two_mul_add_one (t : ℕ)).not_two_dvd_nat
  simpa [hawkConductor, hawkDegree, pow_succ, Nat.mul_comm] using hc

/-- Distinct indices give distinct odd powers below the conductor. -/
theorem oddPrimitiveRoot_injective (k : ℕ) (ξ : C)
    (hξ : IsPrimitiveRoot ξ (hawkConductor k)) :
    Function.Injective (oddPrimitiveRoot k ξ hξ) := by
  intro i j hij
  have hpows : ξ ^ (2 * (i : ℕ) + 1) = ξ ^ (2 * (j : ℕ) + 1) :=
    congrArg Subtype.val hij
  have hi : 2 * (i : ℕ) + 1 < (hawkConductor k : ℕ) := by
    rw [hawkConductor_coe]
    have := i.isLt
    omega
  have hj : 2 * (j : ℕ) + 1 < (hawkConductor k : ℕ) := by
    rw [hawkConductor_coe]
    have := j.isLt
    omega
  have he := hξ.pow_inj hi hj hpows
  apply Fin.ext
  omega

/-- The odd powers enumerate all primitive roots of the power-of-two conductor. -/
noncomputable def oddPrimitiveEquiv (k : ℕ) (ξ : C)
    (hξ : IsPrimitiveRoot ξ (hawkConductor k)) :
    Fin (hawkDegree k) ≃ ↥(primitiveRoots (hawkConductor k) C) := by
  let f := oddPrimitiveRoot k ξ hξ
  have hinj : Function.Injective f := oddPrimitiveRoot_injective k ξ hξ
  have hcard :
      Fintype.card (Fin (hawkDegree k)) =
        Fintype.card ↥(primitiveRoots (hawkConductor k) C) := by
    rw [Fintype.card_fin, Fintype.card_coe, hξ.card_primitiveRoots,
      totient_hawkConductor]
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, hcard⟩
  exact Equiv.ofBijective f hbij

@[simp]
theorem oddPrimitiveEquiv_apply_coe (k : ℕ) (ξ : C)
    (hξ : IsPrimitiveRoot ξ (hawkConductor k)) (t : Fin (hawkDegree k)) :
    ((oddPrimitiveEquiv k ξ hξ t : ↥(primitiveRoots (hawkConductor k) C)) : C) =
      ξ ^ (2 * (t : ℕ) + 1) := rfl

end OddEmbeddings

section CyclotomicTrace

variable {E : Type*} [Field E] [Algebra ℚ E]

/-- The cyclotomic extension has rational degree `2^k`. -/
theorem finrank_hawkCyclotomic (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] :
    Module.finrank ℚ E = hawkDegree k := by
  letI := IsCyclotomicExtension.finiteDimensional {hawkConductor k} ℚ E
  rw [IsCyclotomicExtension.finrank E
    (cyclotomic.irreducible_rat (hawkConductor k).2)]
  exact totient_hawkConductor k

/--
For `0 < j < n`, the actual field trace of `ζ^j` is zero.  This is the
end-to-end version of the embedding sum: Mathlib's
`trace_eq_sum_embeddings` is reindexed by primitive roots, those roots are
reindexed by the odd powers, and the finite geometric sum is then evaluated.
-/
theorem trace_pow_eq_zero_hawk (k : ℕ) (ζ : E)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (hζ : IsPrimitiveRoot ζ (hawkConductor k))
    {j : ℕ} (hj0 : 0 < j) (hjn : j < hawkDegree k) :
    Algebra.trace ℚ E (ζ ^ j) = 0 := by
  classical
  letI := IsCyclotomicExtension.finiteDimensional {hawkConductor k} ℚ E
  letI := IsCyclotomicExtension.isGalois (hawkConductor k) ℚ E
  let C := AlgebraicClosure E
  let ξ : C := algebraMap E C ζ
  have hξ : IsPrimitiveRoot ξ (hawkConductor k) := by
    exact hζ.map_of_injective (algebraMap E C).injective
  have hirr : Irreducible (cyclotomic (hawkConductor k) ℚ) :=
    cyclotomic.irreducible_rat (hawkConductor k).2
  apply (algebraMap ℚ C).injective
  rw [map_zero, trace_eq_sum_embeddings C]
  calc
    (∑ σ : E →ₐ[ℚ] C, σ (ζ ^ j)) =
        ∑ η : ↥(primitiveRoots (hawkConductor k) C), (η : C) ^ j := by
          apply Fintype.sum_equiv (hζ.embeddingsEquivPrimitiveRoots C hirr)
          intro σ
          simpa only [map_pow] using
            congrArg (fun x : C => x ^ j)
              (hζ.embeddingsEquivPrimitiveRoots_apply_coe C hirr σ).symm
    _ = ∑ t : Fin (hawkDegree k), ξ ^ ((2 * (t : ℕ) + 1) * j) := by
          symm
          apply Fintype.sum_equiv (oddPrimitiveEquiv k ξ hξ)
          intro t
          calc
            ξ ^ ((2 * (t : ℕ) + 1) * j) =
                (ξ ^ (2 * (t : ℕ) + 1)) ^ j := by
                  rw [pow_mul]
            _ = ((oddPrimitiveEquiv k ξ hξ t :
                  ↥(primitiveRoots (hawkConductor k) C)) : C) ^ j := by
                  exact congrArg (fun x : C => x ^ j)
                    (oddPrimitiveEquiv_apply_coe k ξ hξ t).symm
    _ = ∑ t ∈ Finset.range (hawkDegree k), ξ ^ ((2 * t + 1) * j) := by
          rw [Fin.sum_univ_eq_sum_range
            (fun t => ξ ^ ((2 * t + 1) * j)) (hawkDegree k)]
    _ = 0 := by
          have hξ' : IsPrimitiveRoot ξ (2 * hawkDegree k) := by
            simpa [hawkConductor] using hξ
          exact odd_power_sum_zero_of_primitive hξ' hj0 hjn

/-- The normalized trace of `1` is one in the HAWK cyclotomic field. -/
theorem normalizedTraceQ_one_hawk (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] :
    normalizedTraceQ (E := E) (hawkDegree k) 1 = 1 := by
  letI := IsCyclotomicExtension.finiteDimensional {hawkConductor k} ℚ E
  change (hawkDegree k : ℚ)⁻¹ * Algebra.trace ℚ E 1 = 1
  rw [show (1 : E) = algebraMap ℚ E 1 by simp, Algebra.trace_algebraMap]
  rw [finrank_hawkCyclotomic (E := E) k]
  simp [(hawkDegree_pos k).ne']

/-- The normalized trace of every nontrivial power below `n` is zero. -/
theorem normalizedTraceQ_pow_eq_zero_hawk (k : ℕ) (ζ : E)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (hζ : IsPrimitiveRoot ζ (hawkConductor k))
    {j : ℕ} (hj0 : 0 < j) (hjn : j < hawkDegree k) :
    normalizedTraceQ (E := E) (hawkDegree k) (ζ ^ j) = 0 := by
  letI := IsCyclotomicExtension.finiteDimensional {hawkConductor k} ℚ E
  change (hawkDegree k : ℚ)⁻¹ * Algebra.trace ℚ E (ζ ^ j) = 0
  rw [trace_pow_eq_zero_hawk (E := E) k ζ hζ hj0 hjn, mul_zero]

/--
The trace-orthogonality relation is a theorem of the concrete cyclotomic
setting; it is no longer an assumption.
-/
theorem traceOrthogonality_hawk (k : ℕ) (ζ : E)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (hζ : IsPrimitiveRoot ζ (hawkConductor k)) :
    TraceOrthogonality (E := E) (n := hawkDegree k) ζ := by
  letI := IsCyclotomicExtension.finiteDimensional {hawkConductor k} ℚ E
  intro i j
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (hawkConductor k).2.ne'
    have hprod : (ζ⁻¹) ^ (i : ℕ) * ζ ^ (i : ℕ) = 1 := by
      rw [inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero _ hζ0)
    rw [hprod]
    exact normalizedTraceQ_one_hawk (E := E) k
  · rw [if_neg hij]
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (hawkConductor k).2.ne'
    by_cases hijlt : (i : ℕ) < (j : ℕ)
    · have hprod :
          (ζ⁻¹) ^ (i : ℕ) * ζ ^ (j : ℕ) = ζ ^ ((j : ℕ) - (i : ℕ)) := by
        rw [inv_pow]
        have hsub := pow_sub₀ ζ hζ0 (Nat.le_of_lt hijlt)
        calc
          (ζ ^ (i : ℕ))⁻¹ * ζ ^ (j : ℕ) =
              ζ ^ (j : ℕ) * (ζ ^ (i : ℕ))⁻¹ := by rw [mul_comm]
          _ = ζ ^ ((j : ℕ) - (i : ℕ)) := hsub.symm
      rw [hprod]
      apply normalizedTraceQ_pow_eq_zero_hawk (E := E) k ζ hζ
      · omega
      · have hi := i.isLt
        have hj := j.isLt
        omega
    · have hjilt : (j : ℕ) < (i : ℕ) := by
        have hine : (i : ℕ) ≠ (j : ℕ) := by
          intro h
          exact hij (Fin.ext h)
        omega
      have hprod :
          (ζ⁻¹) ^ (i : ℕ) * ζ ^ (j : ℕ) =
            (ζ⁻¹) ^ ((i : ℕ) - (j : ℕ)) := by
        have hζinv0 : ζ⁻¹ ≠ 0 := inv_ne_zero hζ0
        have hsub := pow_sub₀ (ζ⁻¹) hζinv0 (Nat.le_of_lt hjilt)
        calc
          (ζ⁻¹) ^ (i : ℕ) * ζ ^ (j : ℕ) =
              (ζ⁻¹) ^ (i : ℕ) * ((ζ⁻¹) ^ (j : ℕ))⁻¹ := by
                simp [inv_pow, hζ0]
          _ = (ζ⁻¹) ^ ((i : ℕ) - (j : ℕ)) := hsub.symm
      rw [hprod]
      apply normalizedTraceQ_pow_eq_zero_hawk (E := E) k (ζ⁻¹) hζ.inv
      · omega
      · have hi := i.isLt
        have hj := j.isLt
        omega

/-- Dot-product identity with trace orthogonality fully discharged. -/
theorem normalized_trace_coeff_pairing_hawk (k : ℕ) (ζ : E)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (hζ : IsPrimitiveRoot ζ (hawkConductor k))
    (a b : Fin (hawkDegree k) → ℚ) :
    normalizedTraceQ (E := E) (hawkDegree k)
        (coeffConjExpansion ζ a * coeffExpansion ζ b) =
      ∑ i, a i * b i := by
  letI := IsCyclotomicExtension.finiteDimensional {hawkConductor k} ℚ E
  exact normalized_trace_coeff_pairing ζ (traceOrthogonality_hawk k ζ hζ) a b

/-! ### The actual cyclotomic conjugation -/

/-- The canonical primitive root chosen by Mathlib for this cyclotomic extension. -/
noncomputable def hawkZeta (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] : E :=
  IsCyclotomicExtension.zeta (hawkConductor k) ℚ E

@[simp]
theorem hawkZeta_spec (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] :
    IsPrimitiveRoot (hawkZeta (E := E) k) (hawkConductor k) := by
  exact IsCyclotomicExtension.zeta_spec (hawkConductor k) ℚ E

/--
The cyclotomic automorphism sending `ζ` to `ζ⁻¹`.  In the intended complex
realization this is complex conjugation.
-/
noncomputable def cyclotomicConjugation (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] : E ≃ₐ[ℚ] E :=
  IsCyclotomicExtension.fromZetaAut
    (K := ℚ) (L := E)
    (IsCyclotomicExtension.zeta_spec (hawkConductor k) ℚ E).inv
    (cyclotomic.irreducible_rat (hawkConductor k).2)

@[simp]
theorem cyclotomicConjugation_zeta (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] :
    cyclotomicConjugation (E := E) k (hawkZeta (E := E) k) =
      (hawkZeta (E := E) k)⁻¹ := by
  simpa [cyclotomicConjugation, hawkZeta] using
    (IsCyclotomicExtension.fromZetaAut_spec
      (K := ℚ) (L := E)
      (IsCyclotomicExtension.zeta_spec (hawkConductor k) ℚ E).inv
      (cyclotomic.irreducible_rat (hawkConductor k).2))

/-- Conjugation acts coefficientwise by replacing `ζ` with `ζ⁻¹`. -/
theorem cyclotomicConjugation_coeffExpansion (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (a : Fin (hawkDegree k) → ℚ) :
    cyclotomicConjugation (E := E) k
        (coeffExpansion (hawkZeta (E := E) k) a) =
      coeffConjExpansion (hawkZeta (E := E) k) a := by
  unfold coeffExpansion coeffConjExpansion
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let e : E ≃ₐ[ℚ] E := cyclotomicConjugation (E := E) k
  change
    e (a i • (hawkZeta (E := E) k) ^ (i : ℕ)) =
      a i • ((hawkZeta (E := E) k)⁻¹) ^ (i : ℕ)
  calc
    e (a i • (hawkZeta (E := E) k) ^ (i : ℕ)) =
        e ((algebraMap ℚ E (a i)) *
          (hawkZeta (E := E) k) ^ (i : ℕ)) := by
            rw [Algebra.smul_def]
    _ = e (algebraMap ℚ E (a i)) *
          e ((hawkZeta (E := E) k) ^ (i : ℕ)) := by
            rw [map_mul]
    _ = (algebraMap ℚ E (a i)) *
          (e (hawkZeta (E := E) k)) ^ (i : ℕ) := by
            rw [AlgEquiv.commutes, map_pow]
    _ = (algebraMap ℚ E (a i)) *
          ((hawkZeta (E := E) k)⁻¹) ^ (i : ℕ) := by
            dsimp [e]
            rw [cyclotomicConjugation_zeta]
    _ = a i • ((hawkZeta (E := E) k)⁻¹) ^ (i : ℕ) := by
            rw [Algebra.smul_def]

/--
**End-to-end cyclotomic trace identity.** For the actual power-of-two cyclotomic
extension and its actual conjugation automorphism, normalized field trace is
the Euclidean coefficient inner product.
-/
theorem cyclotomic_trace_coeff_inner (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (a b : Fin (hawkDegree k) → ℚ) :
    normalizedTraceQ (E := E) (hawkDegree k)
        (cyclotomicConjugation (E := E) k
            (coeffExpansion (hawkZeta (E := E) k) a) *
          coeffExpansion (hawkZeta (E := E) k) b) =
      ∑ i, a i * b i := by
  letI := IsCyclotomicExtension.finiteDimensional {hawkConductor k} ℚ E
  rw [cyclotomicConjugation_coeffExpansion]
  exact normalized_trace_coeff_pairing_hawk
    k (hawkZeta (E := E) k) (hawkZeta_spec (E := E) k) a b

/--
**Equation (2.2), end to end.**  The normalized trace of `a^* a` is the sum
of squares of the rational power-basis coefficients.
-/
theorem cyclotomic_trace_coeff_sq (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (a : Fin (hawkDegree k) → ℚ) :
    normalizedTraceQ (E := E) (hawkDegree k)
        (cyclotomicConjugation (E := E) k
            (coeffExpansion (hawkZeta (E := E) k) a) *
          coeffExpansion (hawkZeta (E := E) k) a) =
      ∑ i, (a i) ^ 2 := by
  simpa [pow_two] using
    cyclotomic_trace_coeff_inner (E := E) k a a

end CyclotomicTrace
end Hawk.CyclotomicTrace
