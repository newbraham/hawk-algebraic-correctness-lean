import Hawk.Geometry

/-!
# The HAWK public key

The cyclotomic involution preserves the integer coefficient ring. Hence a
public Gram matrix computed from an integral secret basis remains integral.
We also identify each entry of the rank-two Gram matrix explicitly.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Matrix
open Matrix

namespace Hawk.PublicKey

open Hawk.CyclotomicTrace Hawk.CyclotomicSigning Hawk.Concrete

variable {E : Type*} [Field E] [Algebra ℚ E]

/-- The inverse of the primitive root is again in the coefficient ring. -/
theorem zeta_inv_mem_coeffRing (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] :
    (hawkZeta (E := E) k)⁻¹ ∈ coeffRing (E := E) k := by
  let ζ := hawkZeta (E := E) k
  let m : ℕ := hawkConductor k
  have hm : 1 ≤ m := by exact Nat.one_le_iff_ne_zero.mpr (PNat.ne_zero _)
  have hmul : ζ ^ (m - 1) * ζ = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
    exact (hawkZeta_spec (E := E) k).pow_eq_one
  have hpow : ζ⁻¹ = ζ ^ (m - 1) :=
    (eq_inv_of_mul_eq_one_left hmul).symm
  rw [hpow]
  exact (coeffRing (E := E) k).pow_mem (hawkZeta_mem_coeffRing (E := E) k) _

/-- Conjugation preserves `ℤ[ζ]`. -/
theorem conjugation_mem_coeffRing (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] (x : E)
    (hx : x ∈ coeffRing (E := E) k) :
    cyclotomicConjugation (E := E) k x ∈ coeffRing (E := E) k := by
  let c := cyclotomicConjugation (E := E) k
  have hle : coeffRing (E := E) k ≤
      (coeffRing (E := E) k).comap c.toRingHom := by
    apply Subring.closure_le.mpr
    intro y hy
    have hy' : y = hawkZeta (E := E) k := Set.mem_singleton_iff.mp hy
    subst y
    change c (hawkZeta (E := E) k) ∈ coeffRing (E := E) k
    simpa [c, cyclotomicConjugation_zeta] using
      (zeta_inv_mem_coeffRing (E := E) k)
  exact hle hx

/-- Every public Gram entry belongs to `ℤ[ζ]` if every secret entry does. -/
theorem gram_entries_integral (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    {ι : Type*} [Fintype ι] (B : Matrix ι ι E)
    (hB : Hawk.IntegralMat (coeffRing (E := E) k) B) :
    Hawk.IntegralMat (coeffRing (E := E) k)
      (cyclotomicGram (E := E) k B) := by
  intro i j
  change (∑ t, cyclotomicConjugation (E := E) k (B t i) * B t j) ∈
    coeffRing (E := E) k
  apply Subring.sum_mem
  intro t ht
  exact (coeffRing (E := E) k).mul_mem
    (conjugation_mem_coeffRing (E := E) k (B t i) (hB t i)) (hB t j)

/-- The actual cyclotomic public Gram matrix is Hermitian. -/
theorem gram_hermitian (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    {ι : Type*} [Fintype ι] (B : Matrix ι ι E) :
    cyclotomicConjTranspose (E := E) k (cyclotomicGram (E := E) k B) =
      cyclotomicGram (E := E) k B := by
  letI : StarRing E := cyclotomicStarRing (E := E) k
  change (Bᴴ * B)ᴴ = Bᴴ * B
  exact Hawk.gram_hermitian B

/-- Explicit entries of the rank-two NTRU public key `Bᴴ B`. -/
theorem keyMatrix_gram (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (f F g G : E) :
    cyclotomicGram (E := E) k (keyMatrix f F g G) =
      !![cyclotomicConjugation (E := E) k f * f +
            cyclotomicConjugation (E := E) k g * g,
          cyclotomicConjugation (E := E) k f * F +
            cyclotomicConjugation (E := E) k g * G;
         cyclotomicConjugation (E := E) k F * f +
            cyclotomicConjugation (E := E) k G * g,
          cyclotomicConjugation (E := E) k F * F +
            cyclotomicConjugation (E := E) k G * G] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclotomicGram, cyclotomicConjTranspose, keyMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The rank-two Gram quadratic form is positive definite under `fG - gF = 1`. -/
theorem keyMatrix_gram_eq_zero_iff (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (f F g G : E) (hdet : f * G - g * F = 1) (v : Fin 2 → E) :
    cyclotomicPublicSq (E := E) k
      (cyclotomicGram (E := E) k (keyMatrix f F g G)) v = 0 ↔ v = 0 := by
  simpa only [keyBasis_val] using
    (Hawk.Geometry.publicSq_gram_eq_zero_iff (E := E) k (keyBasis f F g G hdet) v)

end Hawk.PublicKey
