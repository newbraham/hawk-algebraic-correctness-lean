import Hawk.Concrete
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false
open scoped BigOperators Matrix
open Matrix

namespace Hawk.Functional

open Hawk.CyclotomicTrace
open Hawk.CyclotomicSigning
open Hawk.Concrete

variable {E : Type*} [Field E] [Algebra ℚ E]

/-! ## Rational-coordinate sign canonicalization -/

/-- First-nonzero-rational-coordinate-positive sign convention. -/
def CoeffSymBreak {n : ℕ} (a : Fin n → ℚ) : Prop :=
  ∃ i : Fin n, (∀ j : Fin n, j < i → a j = 0) ∧ 0 < a i

/-- Every nonzero coefficient vector or its negation satisfies the convention. -/
theorem coeffSymBreak_or_neg {n : ℕ} (a : Fin n → ℚ)
    (hne : ∃ i, a i ≠ 0) : CoeffSymBreak a ∨ CoeffSymBreak (-a) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => a i ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [S, hi]⟩
  let i : Fin n := S.min' hS
  have hiS : i ∈ S := Finset.min'_mem S hS
  have hi0 : a i ≠ 0 := by
    simpa [S] using hiS
  have hprev : ∀ j : Fin n, j < i → a j = 0 := by
    intro j hj
    by_contra hj0
    have hjS : j ∈ S := by simp [S, hj0]
    have hij : i ≤ j := Finset.min'_le S j hjS
    exact (not_le_of_gt hj) hij
  rcases lt_or_gt_of_ne hi0.symm with hpos | hneg
  · exact Or.inl ⟨i, hprev, hpos⟩
  · right
    refine ⟨i, ?_, ?_⟩
    · intro j hj
      simp [hprev j hj]
    · change 0 < -a i
      linarith

/--
Rational-coordinate analogue of HAWK's sign convention on the second
polynomial. Identifying it with the specification's integer-coefficient
predicate requires the separate integer-coordinate bridge.
-/
def symBreak (k : ℕ) [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (w : Fin 2 → E) : Prop :=
  CoeffSymBreak (coeffs (E := E) k (w 1))

/-- Choose the sign prescribed by `sym-break`. -/
noncomputable def canonicalW (k : ℕ) [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (w : Fin 2 → E) : Fin 2 → E :=
  @ite (Fin 2 → E) (symBreak (E := E) k w)
    (Classical.propDecidable _) w (-w)

/-- Except for the all-zero second polynomial, canonicalization satisfies `sym-break`. -/
theorem symBreak_canonicalW (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (w : Fin 2 → E)
    (hne : ∃ i, coeffs (E := E) k (w 1) i ≠ 0) :
    symBreak (E := E) k (canonicalW (E := E) k w) := by
  classical
  by_cases hsb : CoeffSymBreak (coeffs (E := E) k (w 1))
  · have hw : canonicalW (E := E) k w = w := by
      simp [canonicalW, symBreak, hsb]
    rw [hw]
    exact hsb
  · have hor := coeffSymBreak_or_neg (coeffs (E := E) k (w 1)) hne
    have hneg : CoeffSymBreak (-coeffs (E := E) k (w 1)) := hor.resolve_left hsb
    have hw : canonicalW (E := E) k w = -w := by
      simp [canonicalW, symBreak, hsb]
    rw [hw]
    unfold symBreak
    simp only [Pi.neg_apply]
    rw [coeffs_neg]
    exact hneg

/-! ## Abstract projection/rebuild interface -/

/-- Projection interface: retain the second signature component s1. -/
def compress (s : Fin 2 → E) : E := s 1

/--
Shape of an external rebuild oracle. It receives Q, h0, and
w1 = h1 - 2*s1, may fail, and returns a candidate w0. This does not
formalize HAWK's concrete fixed-point/rounding algorithm or prove that the
oracle is independent of secret data.
-/
abbrev RebuildW0 := Matrix (Fin 2) (Fin 2) E → E → E → Option E

/-- Attempt reconstruction through the failure-aware abstract rebuild oracle. -/
def decompress (Q : Matrix (Fin 2) (Fin 2) E) (h : Fin 2 → E)
    (rebuildW0 : RebuildW0 (E := E)) (s1 : E) : Option (Fin 2 → E) :=
  let w1 := h 1 - (2 : E) * s1
  match rebuildW0 Q (h 0) w1 with
  | none => none
  | some w0 => some ![(h 0 - w0) / (2 : E), s1]

omit [Algebra ℚ E] in
/-- Exactness conditional on the rebuild oracle returning the exact first preimage coordinate. -/
theorem decompress_compress_of_rebuild
    [CharZero E]
    (Q : Matrix (Fin 2) (Fin 2) E) (h s : Fin 2 → E)
    (rebuildW0 : RebuildW0 (E := E))
    (hrebuild :
      rebuildW0 Q (h 0) (h 1 - (2 : E) * s 1) =
        some (h 0 - (2 : E) * s 0)) :
    decompress Q h rebuildW0 (compress s) = some s := by
  simp [decompress, compress, hrebuild]
  ext i
  fin_cases i <;> rfl

/-! ## Canonical signer branch -/

variable [CharZero E]

/-- The full signature after the HAWK sign-choice step. -/
noncomputable def canonicalSignature (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (B : (Matrix (Fin 2) (Fin 2) E)ˣ) (h x : Fin 2 → E) : Fin 2 → E :=
  @ite (Fin 2 → E) (symBreak (E := E) k (Hawk.preimage B x))
    (Classical.propDecidable _) (Hawk.signature B h x)
    (h - Hawk.signature B h x)

/-- Public reconstruction of the canonical branch is exactly the sign-canonical preimage. -/
theorem reconstruction_canonicalSignature (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (B : (Matrix (Fin 2) (Fin 2) E)ˣ) (h x : Fin 2 → E) :
    h - (2 : E) • canonicalSignature (E := E) k B h x =
      canonicalW (E := E) k (Hawk.preimage B x) := by
  classical
  by_cases hsb : symBreak (E := E) k (Hawk.preimage B x)
  · simpa [canonicalSignature, canonicalW, hsb] using Hawk.reconstruction B h x
  · have hr := Hawk.reconstruction_sign_mod 2 (by decide) B h x
    have hflip : Hawk.flippedSignatureMod 2 B h x = h - Hawk.signature B h x :=
      (Hawk.flipped_signature_eq_half B h x).symm
    rw [hflip] at hr
    simpa [canonicalSignature, canonicalW, hsb] using hr

/-- The canonical signature remains integral at modulus two. -/
theorem canonicalSignature_integral (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (R : Subring E) (B : (Matrix (Fin 2) (Fin 2) E)ˣ)
    (hBinv : Hawk.IntegralMat R (↑(B⁻¹) : Matrix (Fin 2) (Fin 2) E))
    (h x : Fin 2 → E) (hh : Hawk.IntegralVec R h)
    (hx : Hawk.InSigningCoset R (↑B : Matrix (Fin 2) (Fin 2) E) h x) :
    Hawk.IntegralVec R (canonicalSignature (E := E) k B h x) := by
  classical
  have hs := Hawk.signature_integral R B hBinv h x hx
  by_cases hsb : symBreak (E := E) k (Hawk.preimage B x)
  · simpa [canonicalSignature, hsb] using hs
  · rw [canonicalSignature, if_neg hsb]
    intro i
    exact R.sub_mem (hh i) (hs i)

/-- The reconstructed vector passes symmetry breaking when its second polynomial is nonzero. -/
theorem canonicalSignature_symBreak (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (B : (Matrix (Fin 2) (Fin 2) E)ˣ) (h x : Fin 2 → E)
    (hne : ∃ i, coeffs (E := E) k (Hawk.preimage B x 1) i ≠ 0) :
    symBreak (E := E) k (h - (2 : E) • canonicalSignature (E := E) k B h x) := by
  rw [reconstruction_canonicalSignature]
  exact symBreak_canonicalW (E := E) k (Hawk.preimage B x) hne
-- Concrete cyclotomic public square is invariant under sign.
omit [CharZero E] in
theorem cyclotomicPublicSq_neg (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    {ι : Type*} [Fintype ι] (Q : Matrix ι ι E) (v : ι → E) :
    cyclotomicPublicSq (E := E) k Q (-v) =
      cyclotomicPublicSq (E := E) k Q v := by
  unfold cyclotomicPublicSq
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp [Matrix.mulVec_neg, map_neg]

/-- The canonical sign choice preserves the coefficient-norm equality. -/
theorem canonicalSignature_publicSq (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (R : Subring E) (B : (Matrix (Fin 2) (Fin 2) E)ˣ)
    (hBinv : Hawk.IntegralMat R (↑(B⁻¹) : Matrix (Fin 2) (Fin 2) E))
    (h x : Fin 2 → E)
    (hx : Hawk.InSigningCoset R (↑B : Matrix (Fin 2) (Fin 2) E) h x) :
    let Q := cyclotomicGram (E := E) k (↑B : Matrix (Fin 2) (Fin 2) E)
    cyclotomicPublicSq (E := E) k Q
        (h - (2 : E) • canonicalSignature (E := E) k B h x) =
      coeffSqR k (vectorCoeffs (E := E) k x) := by
  classical
  let Q := cyclotomicGram (E := E) k (↑B : Matrix (Fin 2) (Fin 2) E)
  have hn := signing_correctness_mod_coeff_norm_auto (E := E) 2 (by decide) k
    R B hBinv h x hx
  dsimp only at hn ⊢
  have hnormal :
      cyclotomicPublicSq (E := E) k Q (Hawk.preimage B x) =
        coeffSqR k (vectorCoeffs (E := E) k x) := by
    have hq := hn.2.2.2.2.1
    rw [hn.2.2.1] at hq
    simpa [Q] using hq
  by_cases hsb : symBreak (E := E) k (Hawk.preimage B x)
  · have hrec := reconstruction_canonicalSignature (E := E) k B h x
    rw [hrec]
    simp [canonicalW, hsb]
    exact hnormal
  · have hrec := reconstruction_canonicalSignature (E := E) k B h x
    rw [hrec]
    rw [show canonicalW (E := E) k (Hawk.preimage B x) = -Hawk.preimage B x by
      simp [canonicalW, hsb]]
    rw [cyclotomicPublicSq_neg]
    exact hnormal


/-! ## Conditional post-hash composition -/

/--
Deterministic checks after an externally supplied vector h, intended to be hash-derived.
externalValid represents a validity condition established outside this
algebraic development. Parsing, hashing, encoding, and the concrete rebuild
algorithm are not modeled.
-/
def PostHashChecks (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (R : Subring E) (Q : Matrix (Fin 2) (Fin 2) E) (h : Fin 2 → E)
    (rebuildW0 : RebuildW0 (E := E)) (externalValid : Prop)
    (bound : ℝ) (s1 : E) : Prop :=
  externalValid ∧
    ∃ s, decompress Q h rebuildW0 s1 = some s ∧
      Hawk.IntegralVec R s ∧ symBreak (E := E) k (h - (2 : E) • s) ∧
      cyclotomicPublicSq (E := E) k Q (h - (2 : E) • s) ≤ bound

/-- Exact abstract rebuilding plus the deterministic checks imply post-hash acceptance. -/
theorem postHashChecks_compress (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (R : Subring E) (Q : Matrix (Fin 2) (Fin 2) E) (h s : Fin 2 → E)
    (rebuildW0 : RebuildW0 (E := E)) (externalValid : Prop) (bound : ℝ)
    (hvalid : externalValid)
    (hrebuild :
      rebuildW0 Q (h 0) (h 1 - (2 : E) * s 1) =
        some (h 0 - (2 : E) * s 0))
    (hs : Hawk.IntegralVec R s)
    (hsym : symBreak (E := E) k (h - (2 : E) • s))
    (hbound : cyclotomicPublicSq (E := E) k Q (h - (2 : E) • s) ≤ bound) :
    PostHashChecks (E := E) k R Q h rebuildW0 externalValid bound (compress s) := by
  refine ⟨hvalid, s, ?_, hs, hsym, hbound⟩
  exact decompress_compress_of_rebuild (E := E) Q h s rebuildW0 hrebuild

/--
Conditional post-hash endpoint for the HAWK-shaped rank-two algebraic pipeline.
It composes the NTRU-derived basis, an explicit signing-coset witness, rational
coefficient extraction, sign canonicalization, the abstract rebuild interface,
and deterministic checks. The binary restriction on the hash output, the
probabilistic sampler, concrete RebuildS0, parsing/encoding, and derivation of
external validity and norm-bound facts remain outside this theorem.
-/
theorem hawk_rank2_conditional_postHash_acceptance (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (f F g G : coeffRing (E := E) k)
    (hdet : f * G - g * F = 1)
    (h0 z0 : Fin 2 → coeffRing (E := E) k)
    (rebuildW0 : RebuildW0 (E := E))
    (externalValid : Prop) (hvalid : externalValid) (bound : ℝ)
    (hne :
      let R := coeffRing (E := E) k
      let B0 := keyBasis f F g G hdet
      let B := Hawk.ambientBasis R B0
      let x := cosetPoint R B0 h0 z0
      ∃ i, coeffs (E := E) k (Hawk.preimage B x 1) i ≠ 0)
    (hrebuild :
      let R := coeffRing (E := E) k
      let B0 := keyBasis f F g G hdet
      let B := Hawk.ambientBasis R B0
      let h : Fin 2 → E := fun i => (h0 i : E)
      let x := cosetPoint R B0 h0 z0
      let Q := cyclotomicGram (E := E) k (↑B : Matrix (Fin 2) (Fin 2) E)
      let s := canonicalSignature (E := E) k B h x
      rebuildW0 Q (h 0) (h 1 - (2 : E) * s 1) =
        some (h 0 - (2 : E) * s 0))
    (hbound :
      let R := coeffRing (E := E) k
      let B0 := keyBasis f F g G hdet
      let x := cosetPoint R B0 h0 z0
      coeffSqR k (vectorCoeffs (E := E) k x) ≤ bound) :
    let R := coeffRing (E := E) k
    let B0 := keyBasis f F g G hdet
    let B := Hawk.ambientBasis R B0
    let h : Fin 2 → E := fun i => (h0 i : E)
    let x := cosetPoint R B0 h0 z0
    let Q := cyclotomicGram (E := E) k (↑B : Matrix (Fin 2) (Fin 2) E)
    let s := canonicalSignature (E := E) k B h x
    PostHashChecks (E := E) k R Q h rebuildW0 externalValid bound (compress s) := by
  dsimp only at hne hrebuild hbound ⊢
  let R := coeffRing (E := E) k
  let B0 := keyBasis f F g G hdet
  let B := Hawk.ambientBasis R B0
  let h : Fin 2 → E := fun i => (h0 i : E)
  let x := cosetPoint R B0 h0 z0
  let Q := cyclotomicGram (E := E) k (↑B : Matrix (Fin 2) (Fin 2) E)
  let s := canonicalSignature (E := E) k B h x
  have hx : Hawk.InSigningCoset R (↑B : Matrix (Fin 2) (Fin 2) E) h x := by
    exact cosetPoint_in_coset (E := E) R B0 h0 z0
  have hh : Hawk.IntegralVec R h := by
    intro i
    exact (h0 i).property
  have hs : Hawk.IntegralVec R s := by
    exact canonicalSignature_integral (E := E) k R B
      (Hawk.ambientBasis_inv_integral R B0) h x hh hx
  have hsym : symBreak (E := E) k (h - (2 : E) • s) := by
    exact canonicalSignature_symBreak (E := E) k B h x hne
  have hsq :
      cyclotomicPublicSq (E := E) k Q (h - (2 : E) • s) =
        coeffSqR k (vectorCoeffs (E := E) k x) := by
    simpa [Q, s] using canonicalSignature_publicSq (E := E) k R B
      (Hawk.ambientBasis_inv_integral R B0) h x hx
  have hvbound : cyclotomicPublicSq (E := E) k Q (h - (2 : E) • s) ≤ bound := by
    rw [hsq]
    exact hbound
  exact postHashChecks_compress (E := E) k R Q h s rebuildW0 externalValid bound
    hvalid hrebuild hs hsym hvbound

end Hawk.Functional
