import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Algebraic signing correctness in arbitrary rank

This file isolates the rank-generic algebraic layer used by the HAWK case study.
The lengths below are explicit normalized FIELD TRACE expressions.
The cyclotomic coefficient/trace identification is proved in `Hawk.CyclotomicTrace`
and composed with this generic layer in `Hawk.CyclotomicSigning`.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix
open Matrix

namespace Hawk
variable {E : Type*} [Field E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Membership in R^ι inside E^ι. -/
def IntegralVec (R : Subring E) (v : ι → E) : Prop := ∀ i, v i ∈ R

/-- Entrywise membership in R. -/
def IntegralMat (R : Subring E) (M : Matrix ι ι E) : Prop := ∀ i j, M i j ∈ R

/-- The canonical inclusion GL_ι(R) → GL_ι(E). -/
def ambientBasis (R : Subring E) (B : (Matrix ι ι R)ˣ) : (Matrix ι ι E)ˣ :=
  Units.map R.subtype.mapMatrix.toMonoidHom B

theorem ambientBasis_integral (R : Subring E) (B : (Matrix ι ι R)ˣ) :
    IntegralMat R (↑(ambientBasis R B) : Matrix ι ι E) := by
  intro i j
  exact ((↑B : Matrix ι ι R) i j).property

theorem ambientBasis_inv_integral (R : Subring E) (B : (Matrix ι ι R)ˣ) :
    IntegralMat R (↑((ambientBasis R B)⁻¹) : Matrix ι ι E) := by
  intro i j
  exact ((↑(B⁻¹) : Matrix ι ι R) i j).property

/-- x ∈ Bh + 2R^ι, including the integral coset witness. -/
def InSigningCoset (R : Subring E) (B : Matrix ι ι E) (h x : ι → E) : Prop :=
  ∃ z : ι → E, IntegralVec R z ∧ x = B *ᵥ h + (2 : E) • z

omit [DecidableEq ι] in
theorem integral_mulVec (R : Subring E) (M : Matrix ι ι E) (v : ι → E)
    (hM : IntegralMat R M) (hv : IntegralVec R v) : IntegralVec R (M *ᵥ v) := by
  intro i
  exact R.sum_mem fun j _ => R.mul_mem (hM i j) (hv j)

/-- Inversion is in the GROUP of matrix units. -/
def preimage (B : (Matrix ι ι E)ˣ) (x : ι → E) : ι → E :=
  (↑(B⁻¹) : Matrix ι ι E) *ᵥ x

/-- Division is in E. Membership of the result in R is proved below. -/
def signature (B : (Matrix ι ι E)ˣ) (h x : ι → E) : ι → E :=
  fun i => (h i - preimage B x i) / 2

theorem basis_preimage (B : (Matrix ι ι E)ˣ) (x : ι → E) :
    (↑B : Matrix ι ι E) *ᵥ preimage B x = x := by
  change B.val *ᵥ (B.inv *ᵥ x) = x
  rw [mulVec_mulVec, B.val_inv]
  simp

theorem preimage_from_witness (B : (Matrix ι ι E)ˣ) (h z x : ι → E)
    (hx : x = (↑B : Matrix ι ι E) *ᵥ h + (2 : E) • z) :
    preimage B x = h + (2 : E) • preimage B z := by
  change B.inv *ᵥ x = h + (2 : E) • (B.inv *ᵥ z)
  rw [hx, mulVec_add, mulVec_smul, mulVec_mulVec, B.inv_val]
  simp

variable [CharZero E]

theorem signature_from_witness (B : (Matrix ι ι E)ˣ) (h z x : ι → E)
    (hx : x = (↑B : Matrix ι ι E) *ᵥ h + (2 : E) • z) :
    signature B h x = -preimage B z := by
  have hw := preimage_from_witness B h z x hx
  funext i
  simp only [signature, hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  ring

theorem reconstruction (B : (Matrix ι ι E)ˣ) (h x : ι → E) :
    h - (2 : E) • signature B h x = preimage B x := by
  funext i
  simp only [signature, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem exact_division (B : (Matrix ι ι E)ˣ) (h x : ι → E) :
    h - preimage B x = (2 : E) • signature B h x := by
  funext i
  simp only [signature, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem flipped_signature_eq_half (B : (Matrix ι ι E)ˣ) (h x : ι → E) :
    h - signature B h x = fun i => (h i + preimage B x i) / 2 := by
  funext i
  simp only [signature, Pi.sub_apply]
  ring

theorem signature_integral (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hBinv : IntegralMat R (↑(B⁻¹) : Matrix ι ι E)) (h x : ι → E)
    (hx : InSigningCoset R (↑B : Matrix ι ι E) h x) :
    IntegralVec R (signature B h x) := by
  obtain ⟨z, hz, hx⟩ := hx
  rw [signature_from_witness B h z x hx]
  intro i
  exact R.neg_mem (integral_mulVec R _ z hBinv hz i)

theorem preimage_integral (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hBinv : IntegralMat R (↑(B⁻¹) : Matrix ι ι E)) (h x : ι → E)
    (hh : IntegralVec R h) (hx : InSigningCoset R (↑B : Matrix ι ι E) h x) :
    IntegralVec R (preimage B x) := by
  rw [← reconstruction B h x]
  have hs := signature_integral R B hBinv h x hx
  intro i
  change h i - (2 : E) * signature B h x i ∈ R
  have h2s : (2 : E) * signature B h x i ∈ R := by
    convert R.add_mem (hs i) (hs i) using 1
    ring
  exact R.sub_mem (hh i) h2s

omit [Fintype ι] [DecidableEq ι] in
/-- The exact half is unique in characteristic zero. -/
theorem exact_half_unique (h w s t : ι → E)
    (hs : h - w = (2 : E) • s) (ht : h - w = (2 : E) • t) : s = t := by
  funext i
  have hi := congrFun (hs.symm.trans ht) i
  simpa only [Pi.smul_apply, smul_eq_mul, mul_right_inj' (by norm_num : (2 : E) ≠ 0)]
    using hi

section Metric
variable [StarRing E] [Algebra ℚ E]

/-- Actual field trace, normalized in ℚ by the field degree and then cast to ℝ.
Writing the normalization in ℚ makes later specialization to the cyclotomic
coefficient identity definitionally transparent. -/
def normalizedTrace (a : E) : ℝ :=
  ((((Module.finrank ℚ E : ℕ) : ℚ)⁻¹ * Algebra.trace ℚ E a : ℚ) : ℝ)

def traceSq (v : ι → E) : ℝ := normalizedTrace (star v ⬝ᵥ v)

/-- Public expression: Q alone, with no reference to its secret factor. -/
def publicSq (Q : Matrix ι ι E) (v : ι → E) : ℝ :=
  normalizedTrace (star v ⬝ᵥ (Q *ᵥ v))

def traceLength (v : ι → E) : ℝ := Real.sqrt (traceSq v)
def publicLength (Q : Matrix ι ι E) (v : ι → E) : ℝ := Real.sqrt (publicSq Q v)

omit [CharZero E] [DecidableEq ι] [Algebra ℚ E] in
/-- Proved BEFORE applying the trace or the square root. -/
theorem gram_identity (B : Matrix ι ι E) (v : ι → E) :
    star v ⬝ᵥ ((Bᴴ * B) *ᵥ v) = star (B *ᵥ v) ⬝ᵥ (B *ᵥ v) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

omit [CharZero E] [DecidableEq ι] [Algebra ℚ E] in
theorem gram_hermitian (B : Matrix ι ι E) : (Bᴴ * B)ᴴ = Bᴴ * B := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose]

omit [CharZero E] [DecidableEq ι] in
theorem publicSq_gram (B : Matrix ι ι E) (v : ι → E) :
    publicSq (Bᴴ * B) v = traceSq (B *ᵥ v) := by
  unfold publicSq traceSq
  rw [gram_identity]

omit [CharZero E] [DecidableEq ι] in
theorem publicLength_gram (B : Matrix ι ι E) (v : ι → E) :
    publicLength (Bᴴ * B) v = traceLength (B *ᵥ v) := by
  unfold publicLength traceLength
  rw [publicSq_gram]

omit [CharZero E] [DecidableEq ι] in
theorem publicSq_neg (Q : Matrix ι ι E) (v : ι → E) :
    publicSq Q (-v) = publicSq Q v := by
  simp [publicSq, mulVec_neg]

omit [CharZero E] [DecidableEq ι] in
theorem publicLength_neg (Q : Matrix ι ι E) (v : ι → E) :
    publicLength Q (-v) = publicLength Q v := by
  unfold publicLength
  rw [publicSq_neg]

/-- Rank-generic signing correctness in its normalized-trace formulation.
The two matrix membership hypotheses express B ∈ GL_ι(R) inside GL_ι(E).
Neither Gram transport nor norm equality is assumed. -/
theorem signing_correctness (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (_hB : IntegralMat R (↑B : Matrix ι ι E))
    (hBinv : IntegralMat R (↑(B⁻¹) : Matrix ι ι E))
    (Q : Matrix ι ι E) (hQ : Q = (↑B : Matrix ι ι E)ᴴ * (↑B : Matrix ι ι E))
    (h x : ι → E) (_hh : IntegralVec R h)
    (hx : InSigningCoset R (↑B : Matrix ι ι E) h x) :
    IntegralVec R (signature B h x) ∧
    h - preimage B x = (2 : E) • signature B h x ∧
    h - (2 : E) • signature B h x = preimage B x ∧
    (↑B : Matrix ι ι E) *ᵥ preimage B x = x ∧
    publicSq Q (h - (2 : E) • signature B h x) = traceSq x ∧
    publicLength Q (h - (2 : E) • signature B h x) = traceLength x := by
  refine ⟨signature_integral R B hBinv h x hx, exact_division B h x,
    reconstruction B h x, basis_preimage B x, ?_, ?_⟩
  · rw [reconstruction, hQ, publicSq_gram, basis_preimage]
  · rw [reconstruction, hQ, publicLength_gram, basis_preimage]

/-- Sign-symmetry branch: s' = h-s and w' = -w, including parity and both length identities. -/
theorem signing_correctness_sign (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hBinv : IntegralMat R (↑(B⁻¹) : Matrix ι ι E))
    (Q : Matrix ι ι E) (hQ : Q = (↑B : Matrix ι ι E)ᴴ * (↑B : Matrix ι ι E))
    (h x : ι → E) (hh : IntegralVec R h)
    (hx : InSigningCoset R (↑B : Matrix ι ι E) h x) :
    IntegralVec R (h - signature B h x) ∧
    h - (-preimage B x) = (2 : E) • (h - signature B h x) ∧
    h - (2 : E) • (h - signature B h x) = -preimage B x ∧
    (↑B : Matrix ι ι E) *ᵥ (-preimage B x) = -x ∧
    publicSq Q (h - (2 : E) • (h - signature B h x)) = traceSq x ∧
    publicLength Q (h - (2 : E) • (h - signature B h x)) = traceLength x := by
  have hs := signature_integral R B hBinv h x hx
  have hrec : h - (2 : E) • (h - signature B h x) = -preimage B x := by
    funext i
    have hi := congrFun (reconstruction B h x) i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at *
    linear_combination -hi
  refine ⟨?_, ?_, hrec, ?_, ?_, ?_⟩
  · intro i
    exact R.sub_mem (hh i) (hs i)
  · funext i
    have hi := congrFun hrec i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at *
    linear_combination hi
  · rw [mulVec_neg, basis_preimage]
  · rw [hrec, publicSq_neg, hQ, publicSq_gram, basis_preimage]
  · rw [hrec, publicLength_neg, hQ, publicLength_gram, basis_preimage]

theorem verification_bound (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hB : IntegralMat R (↑B : Matrix ι ι E))
    (hBinv : IntegralMat R (↑(B⁻¹) : Matrix ι ι E))
    (Q : Matrix ι ι E) (hQ : Q = (↑B : Matrix ι ι E)ᴴ * (↑B : Matrix ι ι E))
    (h x : ι → E) (hh : IntegralVec R h)
    (hx : InSigningCoset R (↑B : Matrix ι ι E) h x)
    (bound : ℝ) (hbound : traceSq x ≤ bound) :
    publicSq Q (h - (2 : E) • signature B h x) ≤ bound ∧
    publicSq Q (h - (2 : E) • (h - signature B h x)) ≤ bound := by
  have hp := signing_correctness R B hB hBinv Q hQ h x hh hx
  have hn := signing_correctness_sign R B hBinv Q hQ h x hh hx
  exact ⟨hp.2.2.2.2.1.le.trans hbound, hn.2.2.2.2.1.le.trans hbound⟩

/-- Direct rank-r interface with B over R and a returned signature in R^r.
All entrywise membership properties follow from the input types. -/
theorem signing_correctness_over_ring (r : ℕ) (_hr : 1 ≤ r)
    (R : Subring E) (B₀ : (Matrix (Fin r) (Fin r) R)ˣ)
    (h₀ : Fin r → R) (x : Fin r → E)
    (hx : InSigningCoset R (↑(ambientBasis R B₀) : Matrix (Fin r) (Fin r) E)
      (fun i => (h₀ i : E)) x) :
    let B := ambientBasis R B₀
    let Q := (↑B : Matrix (Fin r) (Fin r) E)ᴴ * (↑B : Matrix (Fin r) (Fin r) E)
    let h : Fin r → E := fun i => (h₀ i : E)
    let w := preimage B x
    ∃ s : Fin r → R,
      (fun i => (s i : E)) = (fun i => (h i - w i) / 2) ∧
      h - (2 : E) • (fun i => (s i : E)) = w ∧
      publicLength Q (h - (2 : E) • (fun i => (s i : E))) = traceLength x ∧
      IntegralVec R (h - (fun i => (s i : E))) ∧
      h - (2 : E) • (h - (fun i => (s i : E))) = -w ∧
      publicLength Q (h - (2 : E) • (h - (fun i => (s i : E)))) = traceLength x := by
  dsimp only
  let B := ambientBasis R B₀
  let h : Fin r → E := fun i => (h₀ i : E)
  have hh : IntegralVec R h := fun i => (h₀ i).property
  have hp := signing_correctness R B (ambientBasis_integral R B₀)
    (ambientBasis_inv_integral R B₀) _ rfl h x hh hx
  have hn := signing_correctness_sign R B (ambientBasis_inv_integral R B₀)
    _ rfl h x hh hx
  refine ⟨fun i => ⟨signature B h x i, hp.1 i⟩, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact hp.2.2.1
  · exact hp.2.2.2.2.2
  · exact hn.1
  · exact hn.2.2.1
  · exact hn.2.2.2.2.2

end Metric
end Hawk
