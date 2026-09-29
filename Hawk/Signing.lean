import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Algebraic signing correctness in arbitrary rank

This file isolates the rank-generic algebraic layer used by the HAWK case study.
Exact division and Gram transport are proved for every positive integer modulus.
The sign-flipped signature is integral exactly when `2h ∈ mR^ι`; HAWK's
modulus-two theorems are specializations of these general results.
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

/-- x ∈ Bh + mR^ι, including the integral coset witness. -/
def InSigningCosetMod (m : ℕ) (R : Subring E) (B : Matrix ι ι E)
    (h x : ι → E) : Prop :=
  ∃ z : ι → E, IntegralVec R z ∧ x = B *ᵥ h + (m : E) • z

/-- HAWK's modulus-two signing coset. -/
def InSigningCoset (R : Subring E) (B : Matrix ι ι E) (h x : ι → E) : Prop :=
  InSigningCosetMod 2 R B h x

/-- v ∈ mR^ι, expressed with an integral divisibility witness. -/
def DivisibleVec (R : Subring E) (m : ℕ) (v : ι → E) : Prop :=
  ∃ t : ι → E, IntegralVec R t ∧ v = (m : E) • t

omit [DecidableEq ι] in
theorem integral_mulVec (R : Subring E) (M : Matrix ι ι E) (v : ι → E)
    (hM : IntegralMat R M) (hv : IntegralVec R v) : IntegralVec R (M *ᵥ v) := by
  intro i
  exact R.sum_mem fun j _ => R.mul_mem (hM i j) (hv j)

/-- Inversion is in the GROUP of matrix units. -/
def preimage (B : (Matrix ι ι E)ˣ) (x : ι → E) : ι → E :=
  (↑(B⁻¹) : Matrix ι ι E) *ᵥ x

/-- Division is in E. The coset condition will imply membership in R. -/
def signatureMod (m : ℕ) (B : (Matrix ι ι E)ˣ) (h x : ι → E) : ι → E :=
  fun i => (h i - preimage B x i) / (m : E)

/-- The signature corresponding to the opposite preimage. -/
def flippedSignatureMod (m : ℕ) (B : (Matrix ι ι E)ˣ) (h x : ι → E) : ι → E :=
  fun i => (h i + preimage B x i) / (m : E)

/-- HAWK's signature is the modulus-two specialization. -/
def signature (B : (Matrix ι ι E)ˣ) (h x : ι → E) : ι → E :=
  signatureMod 2 B h x

theorem basis_preimage (B : (Matrix ι ι E)ˣ) (x : ι → E) :
    (↑B : Matrix ι ι E) *ᵥ preimage B x = x := by
  change B.val *ᵥ (B.inv *ᵥ x) = x
  rw [mulVec_mulVec, B.val_inv]
  simp

theorem preimage_from_witness_mod (m : ℕ) (B : (Matrix ι ι E)ˣ) (h z x : ι → E)
    (hx : x = (↑B : Matrix ι ι E) *ᵥ h + (m : E) • z) :
    preimage B x = h + (m : E) • preimage B z := by
  change B.inv *ᵥ x = h + (m : E) • (B.inv *ᵥ z)
  rw [hx, mulVec_add, mulVec_smul, mulVec_mulVec, B.inv_val]
  simp

theorem preimage_from_witness (B : (Matrix ι ι E)ˣ) (h z x : ι → E)
    (hx : x = (↑B : Matrix ι ι E) *ᵥ h + (2 : E) • z) :
    preimage B x = h + (2 : E) • preimage B z :=
  preimage_from_witness_mod 2 B h z x hx

variable [CharZero E]

theorem signature_from_witness_mod (m : ℕ) (hm : m ≠ 0)
    (B : (Matrix ι ι E)ˣ) (h z x : ι → E)
    (hx : x = (↑B : Matrix ι ι E) *ᵥ h + (m : E) • z) :
    signatureMod m B h x = -preimage B z := by
  have hmE : (m : E) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hw := preimage_from_witness_mod m B h z x hx
  funext i
  simp only [signatureMod, hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  apply (div_eq_iff hmE).2
  ring

theorem signature_from_witness (B : (Matrix ι ι E)ˣ) (h z x : ι → E)
    (hx : x = (↑B : Matrix ι ι E) *ᵥ h + (2 : E) • z) :
    signature B h x = -preimage B z :=
  signature_from_witness_mod 2 (by decide) B h z x hx

theorem reconstruction_mod (m : ℕ) (hm : m ≠ 0)
    (B : (Matrix ι ι E)ˣ) (h x : ι → E) :
    h - (m : E) • signatureMod m B h x = preimage B x := by
  have hmE : (m : E) ≠ 0 := Nat.cast_ne_zero.mpr hm
  funext i
  simp only [signatureMod, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hmE]

theorem reconstruction (B : (Matrix ι ι E)ˣ) (h x : ι → E) :
    h - (2 : E) • signature B h x = preimage B x :=
  reconstruction_mod 2 (by decide) B h x

theorem exact_division_mod (m : ℕ) (hm : m ≠ 0)
    (B : (Matrix ι ι E)ˣ) (h x : ι → E) :
    h - preimage B x = (m : E) • signatureMod m B h x := by
  have hmE : (m : E) ≠ 0 := Nat.cast_ne_zero.mpr hm
  funext i
  simp only [signatureMod, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hmE]

theorem exact_division (B : (Matrix ι ι E)ˣ) (h x : ι → E) :
    h - preimage B x = (2 : E) • signature B h x :=
  exact_division_mod 2 (by decide) B h x

theorem reconstruction_sign_mod (m : ℕ) (hm : m ≠ 0)
    (B : (Matrix ι ι E)ˣ) (h x : ι → E) :
    h - (m : E) • flippedSignatureMod m B h x = -preimage B x := by
  have hmE : (m : E) ≠ 0 := Nat.cast_ne_zero.mpr hm
  funext i
  simp only [flippedSignatureMod, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  field_simp [hmE]

/-- Both candidate signatures sum to an exact quotient of 2h by m. -/
theorem signature_add_flipped_mod (m : ℕ) (hm : m ≠ 0)
    (B : (Matrix ι ι E)ˣ) (h x : ι → E) :
    (m : E) • (signatureMod m B h x + flippedSignatureMod m B h x) = (2 : E) • h := by
  have hmE : (m : E) ≠ 0 := Nat.cast_ne_zero.mpr hm
  funext i
  simp only [signatureMod, flippedSignatureMod, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hmE]
  ring

theorem flipped_signature_eq_half (B : (Matrix ι ι E)ˣ) (h x : ι → E) :
    h - signature B h x = fun i => (h i + preimage B x i) / 2 := by
  funext i
  simp only [signature, signatureMod, Nat.cast_ofNat, Pi.sub_apply]
  ring

theorem signature_integral_mod (m : ℕ) (hm : m ≠ 0)
    (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hBinv : IntegralMat R (↑(B⁻¹) : Matrix ι ι E)) (h x : ι → E)
    (hx : InSigningCosetMod m R (↑B : Matrix ι ι E) h x) :
    IntegralVec R (signatureMod m B h x) := by
  obtain ⟨z, hz, hx⟩ := hx
  rw [signature_from_witness_mod m hm B h z x hx]
  intro i
  exact R.neg_mem (integral_mulVec R _ z hBinv hz i)

theorem signature_integral (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hBinv : IntegralMat R (↑(B⁻¹) : Matrix ι ι E)) (h x : ι → E)
    (hx : InSigningCoset R (↑B : Matrix ι ι E) h x) :
    IntegralVec R (signature B h x) :=
  signature_integral_mod 2 (by decide) R B hBinv h x hx

/-- Under the signing coset condition, the opposite preimage gives an integral
signature if and only if 2h has an integral quotient by m. -/
theorem flipped_signature_integral_iff (m : ℕ) (hm : m ≠ 0)
    (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hBinv : IntegralMat R (↑(B⁻¹) : Matrix ι ι E)) (h x : ι → E)
    (hx : InSigningCosetMod m R (↑B : Matrix ι ι E) h x) :
    IntegralVec R (flippedSignatureMod m B h x) ↔ DivisibleVec R m ((2 : E) • h) := by
  have hs := signature_integral_mod m hm R B hBinv h x hx
  have hmE : (m : E) ≠ 0 := Nat.cast_ne_zero.mpr hm
  constructor
  · intro hf
    exact ⟨signatureMod m B h x + flippedSignatureMod m B h x,
      (fun i => R.add_mem (hs i) (hf i)), (signature_add_flipped_mod m hm B h x).symm⟩
  · rintro ⟨t, ht, hdiv⟩
    have hsum : signatureMod m B h x + flippedSignatureMod m B h x = t := by
      funext i
      have hi := congrFun ((signature_add_flipped_mod m hm B h x).trans hdiv) i
      exact mul_left_cancel₀ hmE hi
    intro i
    have heq : flippedSignatureMod m B h x i = t i - signatureMod m B h x i := by
      have hi := congrFun hsum i
      simp only [Pi.add_apply] at hi
      linear_combination hi
    rw [heq]
    exact R.sub_mem (ht i) (hs i)

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

/-- Exact division, integrality and Gram transport for any positive integer
modulus. The normal branch needs only integrality of the inverse basis and the
integral signing-coset witness. -/
theorem signing_correctness_mod (m : ℕ) (hm : m ≠ 0)
    (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hBinv : IntegralMat R (↑(B⁻¹) : Matrix ι ι E))
    (Q : Matrix ι ι E) (hQ : Q = (↑B : Matrix ι ι E)ᴴ * (↑B : Matrix ι ι E))
    (h x : ι → E)
    (hx : InSigningCosetMod m R (↑B : Matrix ι ι E) h x) :
    IntegralVec R (signatureMod m B h x) ∧
    h - preimage B x = (m : E) • signatureMod m B h x ∧
    h - (m : E) • signatureMod m B h x = preimage B x ∧
    (↑B : Matrix ι ι E) *ᵥ preimage B x = x ∧
    publicSq Q (h - (m : E) • signatureMod m B h x) = traceSq x ∧
    publicLength Q (h - (m : E) • signatureMod m B h x) = traceLength x := by
  refine ⟨signature_integral_mod m hm R B hBinv h x hx, exact_division_mod m hm B h x,
    reconstruction_mod m hm B h x, basis_preimage B x, ?_, ?_⟩
  · rw [reconstruction_mod m hm, hQ, publicSq_gram, basis_preimage]
  · rw [reconstruction_mod m hm, hQ, publicLength_gram, basis_preimage]

/-- HAWK correctness is obtained by specializing the modulus to two. -/
theorem signing_correctness (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hBinv : IntegralMat R (↑(B⁻¹) : Matrix ι ι E))
    (Q : Matrix ι ι E) (hQ : Q = (↑B : Matrix ι ι E)ᴴ * (↑B : Matrix ι ι E))
    (h x : ι → E)
    (hx : InSigningCoset R (↑B : Matrix ι ι E) h x) :
    IntegralVec R (signature B h x) ∧
    h - preimage B x = (2 : E) • signature B h x ∧
    h - (2 : E) • signature B h x = preimage B x ∧
    (↑B : Matrix ι ι E) *ᵥ preimage B x = x ∧
    publicSq Q (h - (2 : E) • signature B h x) = traceSq x ∧
    publicLength Q (h - (2 : E) • signature B h x) = traceLength x :=
  signing_correctness_mod 2 (by decide) R B hBinv Q hQ h x hx

/-- The sign branch for general modulus, with the exact additional condition
`2h ∈ mR^ι`. The metric equalities use the same generic Gram lemmas. -/
theorem signing_correctness_sign_mod (m : ℕ) (hm : m ≠ 0)
    (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hBinv : IntegralMat R (↑(B⁻¹) : Matrix ι ι E))
    (Q : Matrix ι ι E) (hQ : Q = (↑B : Matrix ι ι E)ᴴ * (↑B : Matrix ι ι E))
    (h x : ι → E) (hx : InSigningCosetMod m R (↑B : Matrix ι ι E) h x)
    (hdiv : DivisibleVec R m ((2 : E) • h)) :
    IntegralVec R (flippedSignatureMod m B h x) ∧
    h - (-preimage B x) = (m : E) • flippedSignatureMod m B h x ∧
    h - (m : E) • flippedSignatureMod m B h x = -preimage B x ∧
    (↑B : Matrix ι ι E) *ᵥ (-preimage B x) = -x ∧
    publicSq Q (h - (m : E) • flippedSignatureMod m B h x) = traceSq x ∧
    publicLength Q (h - (m : E) • flippedSignatureMod m B h x) = traceLength x := by
  have hs := (flipped_signature_integral_iff m hm R B hBinv h x hx).2 hdiv
  have hrec := reconstruction_sign_mod m hm B h x
  refine ⟨hs, ?_, hrec, ?_, ?_, ?_⟩
  · funext i
    have hi := congrFun hrec i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at *
    linear_combination hi
  · rw [mulVec_neg, basis_preimage]
  · rw [hrec, publicSq_neg, hQ, publicSq_gram, basis_preimage]
  · rw [hrec, publicLength_neg, hQ, publicLength_gram, basis_preimage]

/-- Modulus two makes the extra sign condition automatic for integral h. -/
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
  have hdiv : DivisibleVec R 2 ((2 : E) • h) := ⟨h, hh, rfl⟩
  have hn := signing_correctness_sign_mod 2 (by decide) R B hBinv Q hQ h x hx hdiv
  have hflip : flippedSignatureMod 2 B h x = h - signature B h x :=
    (flipped_signature_eq_half B h x).symm
  rw [hflip] at hn
  exact hn

theorem verification_bound (R : Subring E) (B : (Matrix ι ι E)ˣ)
    (hBinv : IntegralMat R (↑(B⁻¹) : Matrix ι ι E))
    (Q : Matrix ι ι E) (hQ : Q = (↑B : Matrix ι ι E)ᴴ * (↑B : Matrix ι ι E))
    (h x : ι → E) (hh : IntegralVec R h)
    (hx : InSigningCoset R (↑B : Matrix ι ι E) h x)
    (bound : ℝ) (hbound : traceSq x ≤ bound) :
    publicSq Q (h - (2 : E) • signature B h x) ≤ bound ∧
    publicSq Q (h - (2 : E) • (h - signature B h x)) ≤ bound := by
  have hp := signing_correctness R B hBinv Q hQ h x hx
  have hn := signing_correctness_sign R B hBinv Q hQ h x hh hx
  exact ⟨hp.2.2.2.2.1.le.trans hbound, hn.2.2.2.2.1.le.trans hbound⟩

/-- Direct rank-r interface with B over R and a returned signature in R^r.
All entrywise membership properties follow from the input types. -/
theorem signing_correctness_over_ring (r : ℕ)
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
  have hp := signing_correctness R B
    (ambientBasis_inv_integral R B₀) _ rfl h x hx
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
