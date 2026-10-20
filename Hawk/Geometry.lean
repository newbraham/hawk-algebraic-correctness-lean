import Hawk.Concrete

/-!
# Positive definiteness of the cyclotomic HAWK metric

The coefficient representation is canonical, so the normalized cyclotomic trace
is positive definite on the entire field, not just on explicitly expanded vectors.
The same property transfers to the public Gram form for an invertible basis.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Matrix
open Matrix

namespace Hawk.Geometry

open Hawk.CyclotomicTrace Hawk.CyclotomicSigning Hawk.Concrete

variable {E : Type*} [Field E] [Algebra ℚ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The squared cyclotomic trace norm of any vector equals its squared coefficient norm. -/
theorem traceSq_eq_coeffSqR (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] (v : ι → E) :
    cyclotomicTraceSq (E := E) k v =
      coeffSqR k (vectorCoeffs (E := E) k v) := by
  conv_lhs => rw [← coeffVector_vectorCoeffs (E := E) k v]
  exact cyclotomicTraceSq_coeffVector (E := E) k _

omit [DecidableEq ι] in
/-- Nonnegativity of the actual cyclotomic trace norm. -/
theorem traceSq_nonneg (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] (v : ι → E) :
    0 ≤ cyclotomicTraceSq (E := E) k v := by
  rw [traceSq_eq_coeffSqR]
  exact coeffSqR_nonneg k _

omit [DecidableEq ι] in
/-- The cyclotomic trace form is positive definite on arbitrary field vectors. -/
theorem traceSq_eq_zero_iff (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] (v : ι → E) :
    cyclotomicTraceSq (E := E) k v = 0 ↔ v = 0 := by
  rw [traceSq_eq_coeffSqR, coeffSqR_eq_zero_iff]
  constructor
  · intro h
    have ha : vectorCoeffs (E := E) k v = 0 := by
      funext i j
      exact h i j
    calc
      v = coeffVector (E := E) k (vectorCoeffs (E := E) k v) :=
        (coeffVector_vectorCoeffs (E := E) k v).symm
      _ = 0 := by
        rw [ha]
        ext i
        simp [coeffVector, coeffExpansion]
  · rintro rfl
    simp [vectorCoeffs, coeffs, Basis.equivFun_apply]

omit [DecidableEq ι] in
/-- The concrete public Gram form equals the trace square of `B v`. -/
theorem publicSq_gram (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (B : Matrix ι ι E) (v : ι → E) :
    cyclotomicPublicSq (E := E) k (cyclotomicGram (E := E) k B) v =
      cyclotomicTraceSq (E := E) k (B *ᵥ v) := by
  letI : StarRing E := cyclotomicStarRing (E := E) k
  change cyclotomicTraceR (E := E) k (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)) =
    cyclotomicTraceR (E := E) k (star (B *ᵥ v) ⬝ᵥ (B *ᵥ v))
  rw [Hawk.gram_identity]

omit [DecidableEq ι] in
/-- Nonnegativity of the public Gram quadratic form, even for singular `B`. -/
theorem publicSq_gram_nonneg (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (B : Matrix ι ι E) (v : ι → E) :
    0 ≤ cyclotomicPublicSq (E := E) k (cyclotomicGram (E := E) k B) v := by
  rw [publicSq_gram]
  exact traceSq_nonneg k _

/-- A Gram matrix from an invertible cyclotomic basis is positive definite. -/
theorem publicSq_gram_eq_zero_iff (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (B : (Matrix ι ι E)ˣ) (v : ι → E) :
    cyclotomicPublicSq (E := E) k
      (cyclotomicGram (E := E) k (B : Matrix ι ι E)) v = 0 ↔ v = 0 := by
  rw [publicSq_gram, traceSq_eq_zero_iff]
  constructor
  · intro h
    have hb : ((B⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E) *
        (B : Matrix ι ι E) = 1 := Units.inv_mul B
    calc
      v = (1 : Matrix ι ι E) *ᵥ v := (Matrix.one_mulVec v).symm
      _ = ((B⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E) *ᵥ
          ((B : Matrix ι ι E) *ᵥ v) := by rw [Matrix.mulVec_mulVec, hb]
      _ = 0 := by rw [h, Matrix.mulVec_zero]
  · rintro rfl
    simp

end Hawk.Geometry
