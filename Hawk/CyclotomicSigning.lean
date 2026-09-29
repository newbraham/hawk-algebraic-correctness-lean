import Hawk.Signing
import Hawk.CyclotomicTrace

/-!
# Cyclotomic specialization of signing correctness

This file specializes the generic algebraic correctness proof in
`Hawk.Signing` to the actual power-of-two cyclotomic conjugation used in
the HAWK case study.

The point of this file is that the final metric statement is no longer merely
an equality between two abstract normalized-trace expressions. The cyclotomic
trace identity is invoked to identify the right-hand side with the ordinary Euclidean sum of
squares of the coefficient vectors.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Matrix
open Matrix

namespace Hawk.CyclotomicSigning

open Hawk.CyclotomicTrace

variable {E : Type*} [Field E] [Algebra ℚ E]
variable {ι : Type*} [Fintype ι]

/-! ## Cyclotomic conjugation as a star operation -/

/-- The cyclotomic conjugation from A.1 is an involution. -/
theorem cyclotomicConjugation_involutive (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] :
    Function.Involutive (cyclotomicConjugation (E := E) k) := by
  intro x
  let c := cyclotomicConjugation (E := E) k
  have hcc : c.toAlgHom.comp c.toAlgHom = AlgHom.id ℚ E := by
    apply ((hawkZeta_spec (E := E) k).powerBasis ℚ).algHom_ext
    change c (c (hawkZeta (E := E) k)) = hawkZeta (E := E) k
    rw [show c (hawkZeta (E := E) k) = (hawkZeta (E := E) k)⁻¹ by
      simp [c, cyclotomicConjugation_zeta (E := E) k]]
    rw [map_inv₀]
    rw [show c (hawkZeta (E := E) k) = (hawkZeta (E := E) k)⁻¹ by
      simp [c, cyclotomicConjugation_zeta (E := E) k]]
    simp
  have hx := congrArg (fun f : E →ₐ[ℚ] E => f x) hcc
  simpa [c] using hx

/--
The concrete `StarRing` structure associated with the cyclotomic involution.
It is deliberately a definition rather than a global instance: A.2 installs it
locally, so it cannot conflict with another star structure on the ambient
field.
-/
noncomputable def cyclotomicStarRing (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] : StarRing E where
  star := cyclotomicConjugation (E := E) k
  star_involutive := cyclotomicConjugation_involutive (E := E) k
  star_mul a b := by
    calc
      cyclotomicConjugation (E := E) k (a * b) =
          cyclotomicConjugation (E := E) k a *
            cyclotomicConjugation (E := E) k b := map_mul _ _ _
      _ = cyclotomicConjugation (E := E) k b *
            cyclotomicConjugation (E := E) k a := mul_comm _ _
  star_add a b := map_add _ _ _

/-- Conjugate transpose written without relying on a typeclass star instance. -/
def cyclotomicConjTranspose (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (B : Matrix ι ι E) : Matrix ι ι E :=
  fun i j => cyclotomicConjugation (E := E) k (B j i)

/-- The public Gram matrix `Q = B^⋆ B` for the concrete HAWK involution. -/
def cyclotomicGram (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (B : Matrix ι ι E) : Matrix ι ι E :=
  cyclotomicConjTranspose (E := E) k B * B

/-- A vector assembled from its rational power-basis coefficients. -/
def coeffVector (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (a : ι → Fin (hawkDegree k) → ℚ) : ι → E :=
  fun i => coeffExpansion (hawkZeta (E := E) k) (a i)

/-- Sum of coefficient squares over all module coordinates. -/
def coeffSqQ (k : ℕ) (a : ι → Fin (hawkDegree k) → ℚ) : ℚ :=
  ∑ i, ∑ j, (a i j) ^ 2

/-- The same coefficient squared norm, viewed in `ℝ`. -/
def coeffSqR (k : ℕ) (a : ι → Fin (hawkDegree k) → ℚ) : ℝ :=
  (coeffSqQ k a : ℝ)

/-- The Euclidean coefficient length used in the manuscript. -/
def coeffLength (k : ℕ) (a : ι → Fin (hawkDegree k) → ℚ) : ℝ :=
  Real.sqrt (coeffSqR k a)

/--
Concrete normalized trace as a real number, using the A.1 normalization `1/n`.
-/
def cyclotomicTraceR (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] (y : E) : ℝ :=
  ((normalizedTraceQ (E := E) (hawkDegree k) y : ℚ) : ℝ)

/-- Concrete squared length of a vector under cyclotomic conjugation. -/
def cyclotomicTraceSq (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] (v : ι → E) : ℝ :=
  cyclotomicTraceR (E := E) k
    (∑ i, cyclotomicConjugation (E := E) k (v i) * v i)

/-- Concrete public quadratic form `v^⋆ Q v`. -/
def cyclotomicPublicSq (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (Q : Matrix ι ι E) (v : ι → E) : ℝ :=
  cyclotomicTraceR (E := E) k
    (∑ i, cyclotomicConjugation (E := E) k (v i) * (Q *ᵥ v) i)

/-- Concrete public length. -/
def cyclotomicPublicLength (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (Q : Matrix ι ι E) (v : ι → E) : ℝ :=
  Real.sqrt (cyclotomicPublicSq (E := E) k Q v)

/-! ## Cyclotomic trace identity lifted to vectors -/

/--
This is the coefficient-trace identity lifted coordinatewise to `E^r`.
It identifies the concrete cyclotomic trace square with the ordinary Euclidean
sum of squares of all power-basis coefficients.
-/
theorem cyclotomicTraceSq_coeffVector (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (a : ι → Fin (hawkDegree k) → ℚ) :
    cyclotomicTraceSq (E := E) k (coeffVector (E := E) k a) = coeffSqR k a := by
  unfold cyclotomicTraceSq cyclotomicTraceR coeffSqR coeffSqQ coeffVector
  apply congrArg ((↑) : ℚ → ℝ)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact cyclotomic_trace_coeff_sq (E := E) k (a i)

/-- The coefficient-trace identity also identifies the corresponding square-root expression with Euclidean length. -/
theorem cyclotomicTraceLength_coeffVector (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (a : ι → Fin (hawkDegree k) → ℚ) :
    Real.sqrt (cyclotomicTraceSq (E := E) k (coeffVector (E := E) k a)) =
      coeffLength k a := by
  rw [cyclotomicTraceSq_coeffVector (E := E) k a]
  rfl

/-! ## Signing correctness with the concrete coefficient norm -/

variable [CharZero E] [DecidableEq ι]

/--
**Cyclotomic signing correctness for any positive integer modulus.**

Besides integrality and reconstruction, the public quadratic form is identified
with the actual Euclidean sum of squares of the coefficient vector of `x`.
Thus the final square-root statement is a concrete geometric norm equality,
rather than only an equality of abstract trace expressions.
-/
theorem signing_correctness_mod_coeff_norm (m : ℕ) (hm : m ≠ 0) (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hB : Hawk.IntegralMat R (↑B : Matrix ι ι E))
    (hBinv : Hawk.IntegralMat R (↑(B⁻¹) : Matrix ι ι E))
    (h x : ι → E) (hh : Hawk.IntegralVec R h)
    (hx : Hawk.InSigningCosetMod m R (↑B : Matrix ι ι E) h x)
    (a : ι → Fin (hawkDegree k) → ℚ)
    (hxcoeff : x = coeffVector (E := E) k a) :
    let Q := cyclotomicGram (E := E) k (↑B : Matrix ι ι E)
    let w := Hawk.preimage B x
    let s := Hawk.signatureMod m B h x
    Hawk.IntegralVec R s ∧
      h - w = (m : E) • s ∧
      h - (m : E) • s = w ∧
      (↑B : Matrix ι ι E) *ᵥ w = x ∧
      cyclotomicPublicSq (E := E) k Q (h - (m : E) • s) = coeffSqR k a ∧
      cyclotomicPublicLength (E := E) k Q (h - (m : E) • s) = coeffLength k a := by
  letI := IsCyclotomicExtension.finiteDimensional {hawkConductor k} ℚ E
  letI : StarRing E := cyclotomicStarRing (E := E) k
  dsimp only
  let Q := cyclotomicGram (E := E) k (↑B : Matrix ι ι E)
  have hQ : Q = (↑B : Matrix ι ι E)ᴴ * (↑B : Matrix ι ι E) := by
    rfl
  have hnorm (y : E) :
      Hawk.normalizedTrace y = cyclotomicTraceR (E := E) k y := by
    simp [Hawk.normalizedTrace, cyclotomicTraceR, normalizedTraceQ,
      finrank_hawkCyclotomic (E := E) k, smul_eq_mul]
  have htraceBridge (v : ι → E) :
      Hawk.traceSq v = cyclotomicTraceSq (E := E) k v := by
    unfold Hawk.traceSq cyclotomicTraceSq
    rw [hnorm]
    rfl
  have hpublicBridge (v : ι → E) :
      cyclotomicPublicSq (E := E) k Q v = Hawk.publicSq Q v := by
    unfold cyclotomicPublicSq Hawk.publicSq
    rw [← hnorm]
    rfl
  have hp := Hawk.signing_correctness_mod m hm R B hB hBinv Q hQ h x hh hx
  have hxtrace : Hawk.traceSq x = coeffSqR k a := by
    rw [htraceBridge, hxcoeff]
    exact cyclotomicTraceSq_coeffVector (E := E) k a
  refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, ?_, ?_⟩
  · rw [hpublicBridge]
    exact hp.2.2.2.2.1.trans hxtrace
  · unfold cyclotomicPublicLength coeffLength
    rw [hpublicBridge, hp.2.2.2.2.1, hxtrace]

/-- HAWK's coefficient-norm theorem is a modulus-two corollary. -/
theorem signing_correctness_coeff_norm (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hB : Hawk.IntegralMat R (↑B : Matrix ι ι E))
    (hBinv : Hawk.IntegralMat R (↑(B⁻¹) : Matrix ι ι E))
    (h x : ι → E) (hh : Hawk.IntegralVec R h)
    (hx : Hawk.InSigningCoset R (↑B : Matrix ι ι E) h x)
    (a : ι → Fin (hawkDegree k) → ℚ)
    (hxcoeff : x = coeffVector (E := E) k a) :
    let Q := cyclotomicGram (E := E) k (↑B : Matrix ι ι E)
    let w := Hawk.preimage B x
    let s := Hawk.signature B h x
    Hawk.IntegralVec R s ∧
      h - w = (2 : E) • s ∧
      h - (2 : E) • s = w ∧
      (↑B : Matrix ι ι E) *ᵥ w = x ∧
      cyclotomicPublicSq (E := E) k Q (h - (2 : E) • s) = coeffSqR k a ∧
      cyclotomicPublicLength (E := E) k Q (h - (2 : E) • s) = coeffLength k a :=
  signing_correctness_mod_coeff_norm 2 (by decide) k R B hB hBinv h x hh hx a hxcoeff

/-- The cyclotomic sign branch at general modulus requires `2h ∈ mR^ι`. -/
theorem signing_correctness_sign_mod_coeff_norm (m : ℕ) (hm : m ≠ 0) (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hBinv : Hawk.IntegralMat R (↑(B⁻¹) : Matrix ι ι E))
    (h x : ι → E) (hx : Hawk.InSigningCosetMod m R (↑B : Matrix ι ι E) h x)
    (hdiv : Hawk.DivisibleVec R m ((2 : E) • h))
    (a : ι → Fin (hawkDegree k) → ℚ)
    (hxcoeff : x = coeffVector (E := E) k a) :
    let Q := cyclotomicGram (E := E) k (↑B : Matrix ι ι E)
    let s := Hawk.flippedSignatureMod m B h x
    Hawk.IntegralVec R s ∧
      h - (-Hawk.preimage B x) = (m : E) • s ∧
      h - (m : E) • s = -Hawk.preimage B x ∧
      (↑B : Matrix ι ι E) *ᵥ (-Hawk.preimage B x) = -x ∧
      cyclotomicPublicSq (E := E) k Q (h - (m : E) • s) = coeffSqR k a ∧
      cyclotomicPublicLength (E := E) k Q (h - (m : E) • s) = coeffLength k a := by
  letI := IsCyclotomicExtension.finiteDimensional {hawkConductor k} ℚ E
  letI : StarRing E := cyclotomicStarRing (E := E) k
  dsimp only
  let Q := cyclotomicGram (E := E) k (↑B : Matrix ι ι E)
  have hQ : Q = (↑B : Matrix ι ι E)ᴴ * (↑B : Matrix ι ι E) := by
    rfl
  have hnorm (y : E) :
      Hawk.normalizedTrace y = cyclotomicTraceR (E := E) k y := by
    simp [Hawk.normalizedTrace, cyclotomicTraceR, normalizedTraceQ,
      finrank_hawkCyclotomic (E := E) k, smul_eq_mul]
  have htraceBridge (v : ι → E) :
      Hawk.traceSq v = cyclotomicTraceSq (E := E) k v := by
    unfold Hawk.traceSq cyclotomicTraceSq
    rw [hnorm]
    rfl
  have hpublicBridge (v : ι → E) :
      cyclotomicPublicSq (E := E) k Q v = Hawk.publicSq Q v := by
    unfold cyclotomicPublicSq Hawk.publicSq
    rw [← hnorm]
    rfl
  have hn := Hawk.signing_correctness_sign_mod m hm R B hBinv Q hQ h x hx hdiv
  have hxtrace : Hawk.traceSq x = coeffSqR k a := by
    rw [htraceBridge, hxcoeff]
    exact cyclotomicTraceSq_coeffVector (E := E) k a
  refine ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, ?_, ?_⟩
  · rw [hpublicBridge]
    exact hn.2.2.2.2.1.trans hxtrace
  · unfold cyclotomicPublicLength coeffLength
    rw [hpublicBridge, hn.2.2.2.2.1, hxtrace]

/-- In HAWK the additional divisibility condition has witness h itself. -/
theorem signing_correctness_sign_coeff_norm (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hBinv : Hawk.IntegralMat R (↑(B⁻¹) : Matrix ι ι E))
    (h x : ι → E) (hh : Hawk.IntegralVec R h)
    (hx : Hawk.InSigningCoset R (↑B : Matrix ι ι E) h x)
    (a : ι → Fin (hawkDegree k) → ℚ)
    (hxcoeff : x = coeffVector (E := E) k a) :
    let Q := cyclotomicGram (E := E) k (↑B : Matrix ι ι E)
    let s := Hawk.signature B h x
    Hawk.IntegralVec R (h - s) ∧
      h - (-Hawk.preimage B x) = (2 : E) • (h - s) ∧
      h - (2 : E) • (h - s) = -Hawk.preimage B x ∧
      (↑B : Matrix ι ι E) *ᵥ (-Hawk.preimage B x) = -x ∧
      cyclotomicPublicSq (E := E) k Q (h - (2 : E) • (h - s)) = coeffSqR k a ∧
      cyclotomicPublicLength (E := E) k Q (h - (2 : E) • (h - s)) = coeffLength k a := by
  have hdiv : Hawk.DivisibleVec R 2 ((2 : E) • h) := ⟨h, hh, rfl⟩
  have hn := signing_correctness_sign_mod_coeff_norm 2 (by decide) k R B hBinv
    h x hx hdiv a hxcoeff
  have hflip : Hawk.flippedSignatureMod 2 B h x = h - Hawk.signature B h x :=
    (Hawk.flipped_signature_eq_half B h x).symm
  dsimp only at hn ⊢
  rw [hflip] at hn
  exact hn

end Hawk.CyclotomicSigning
