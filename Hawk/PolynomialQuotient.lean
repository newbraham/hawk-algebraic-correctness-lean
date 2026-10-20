import Hawk.IntegralCoefficients
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The polynomial presentation of the HAWK coefficient ring

For `n = 2^k` the cyclotomic polynomial of conductor `2n` is `X^n + 1`.
The minimal-polynomial presentation of the cyclotomic extension then identifies
the quotient `ℤ[X]/(X^n + 1)` with `ℤ[ζ]`.
-/

noncomputable section
set_option autoImplicit false
open Polynomial

namespace Hawk.PolynomialQuotient

open Hawk.CyclotomicTrace Hawk.Concrete

variable {E : Type*} [Field E] [Algebra ℚ E]

/-- For `n = 2^k`, the `2n`-th cyclotomic polynomial is `X^n + 1`. -/
theorem cyclotomic_hawk_eq (k : ℕ) :
    cyclotomic (hawkConductor k : ℕ) ℤ =
      (X : Polynomial ℤ) ^ hawkDegree k + 1 := by
  have hc : (hawkConductor k : ℕ) = 2 ^ (k + 1) := by
    simp [hawkConductor_coe, hawkDegree, pow_succ, Nat.mul_comm]
  rw [hc, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  simp [Finset.sum_range_succ, hawkDegree, add_comm]

/-- The minimal polynomial of the distinguished primitive root over `ℤ`. -/
theorem minpoly_hawkZeta (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] :
    minpoly ℤ (hawkZeta (E := E) k) =
      (X : Polynomial ℤ) ^ hawkDegree k + 1 := by
  letI : CharZero E :=
    charZero_of_injective_algebraMap (algebraMap ℚ E).injective
  rw [← cyclotomic_eq_minpoly (hawkZeta_spec (E := E) k) (hawkConductor k).pos]
  exact cyclotomic_hawk_eq k

/-- The monogenic HAWK coefficient ring is the indicated polynomial quotient. -/
def adjoinRootEquiv (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] :
    AdjoinRoot ((X : Polynomial ℤ) ^ hawkDegree k + 1) ≃ₐ[ℤ]
      coeffRing (E := E) k := by
  rw [← minpoly_hawkZeta (E := E) k]
  let ζ := hawkZeta (E := E) k
  have hi : IsIntegral ℤ ζ :=
    (hawkZeta_spec (E := E) k).isIntegral (hawkConductor k).pos
  exact (minpoly.equivAdjoin hi).trans
    ((Subring.closureEquivAdjoinInt ({ζ} : Set E)).symm)

/-- Explicit ring isomorphism `ℤ[X]/(X^(2^k) + 1) ≃ ℤ[ζ]`.
    `AdjoinRoot` is definitionally the quotient by the principal ideal. -/
def quotientRingEquiv (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] :
    (Polynomial ℤ ⧸ Ideal.span {((X : Polynomial ℤ) ^ hawkDegree k + 1)}) ≃+*
      coeffRing (E := E) k :=
  (adjoinRootEquiv (E := E) k).toRingEquiv

end Hawk.PolynomialQuotient
