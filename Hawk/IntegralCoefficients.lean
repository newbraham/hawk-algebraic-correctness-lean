import Hawk.PublicKey
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Integral power-basis coordinates in the HAWK coefficient ring

The integral power basis of `ℤ[ζ]` has the same degree as the rational power
basis of the cyclotomic field. This supplies canonical integer coordinates.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace Hawk.IntegralCoefficients

open Hawk.CyclotomicTrace Hawk.Concrete

variable {E : Type*} [Field E] [Algebra ℚ E]

/-- The generator of `ℤ[ζ]` induces an integral power basis. -/
def integralPowerBasis (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] :
    PowerBasis ℤ (coeffRing (E := E) k) := by
  let ζ := hawkZeta (E := E) k
  have hi : IsIntegral ℤ ζ :=
    (hawkZeta_spec (E := E) k).isIntegral (hawkConductor k).pos
  exact (Algebra.adjoin.powerBasis' hi).map
    ((Subring.closureEquivAdjoinInt ({ζ} : Set E)).symm)

/-- The degree of the integral power basis equals the HAWK polynomial degree. -/
theorem integralPowerBasis_dim (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] :
    (integralPowerBasis (E := E) k).dim = hawkDegree k := by
  let ζ := hawkZeta (E := E) k
  have hi : IsIntegral ℤ ζ :=
    (hawkZeta_spec (E := E) k).isIntegral (hawkConductor k).pos
  have hmin : minpoly ℚ ζ = (minpoly ℤ ζ).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hi
  have hdim : (minpoly ℚ ζ).natDegree = hawkDegree k := by
    calc
      (minpoly ℚ ζ).natDegree = ((hawkZeta_spec (E := E) k).powerBasis ℚ).dim :=
        ((hawkZeta_spec (E := E) k).powerBasis_dim ℚ).symm
      _ = Module.finrank ℚ E := ((hawkZeta_spec (E := E) k).powerBasis ℚ).finrank.symm
      _ = hawkDegree k := finrank_hawkCyclotomic (E := E) k
  unfold integralPowerBasis
  rw [PowerBasis.map_dim, Algebra.adjoin.powerBasis'_dim]
  rw [hmin, (minpoly.monic hi).natDegree_map] at hdim
  exact hdim

/-- A basis of `ℤ[ζ]` indexed by `0, ..., n-1`. -/
def integralHawkBasis (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] :
    Basis (Fin (hawkDegree k)) ℤ (coeffRing (E := E) k) :=
  (integralPowerBasis (E := E) k).basis.reindex
    (Fin.castOrderIso (integralPowerBasis_dim (E := E) k)).toEquiv

/-- The integral basis consists of the actual powers of the chosen primitive root. -/
theorem integralHawkBasis_apply (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (i : Fin (hawkDegree k)) :
    ((integralHawkBasis (E := E) k i : coeffRing (E := E) k) : E) =
      hawkZeta (E := E) k ^ (i : ℕ) := by
  let ζ := hawkZeta (E := E) k
  have hi : IsIntegral ℤ ζ :=
    (hawkZeta_spec (E := E) k).isIntegral (hawkConductor k).pos
  have hgen : ((integralPowerBasis (E := E) k).gen : E) = ζ := by
    unfold integralPowerBasis
    rw [PowerBasis.map_gen, Algebra.adjoin.powerBasis'_gen]
    rfl
  change ((((integralPowerBasis (E := E) k).basis.reindex
    (Fin.castOrderIso (integralPowerBasis_dim (E := E) k)).toEquiv) i :
      coeffRing (E := E) k) : E) = _
  rw [Basis.reindex_apply, PowerBasis.basis_eq_pow]
  simpa only [map_pow] using
    congrArg (fun z : E => z ^ (i : ℕ)) hgen

/-- Every coefficient-ring element has an integral coordinate vector. -/
def integerCoeffs (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (x : coeffRing (E := E) k) : Fin (hawkDegree k) → ℤ :=
  (integralHawkBasis (E := E) k).equivFun x

/-- Re-expanding integer coordinates inside the cyclotomic field recovers the element. -/
theorem integer_coeffExpansion (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (x : coeffRing (E := E) k) :
    coeffExpansion (hawkZeta (E := E) k)
      (fun i => (integerCoeffs (E := E) k x i : ℚ)) = (x : E) := by
  let b := integralHawkBasis (E := E) k
  have hrepr := b.sum_repr x
  unfold coeffExpansion
  calc
    (∑ i, (integerCoeffs (E := E) k x i : ℚ) •
       hawkZeta (E := E) k ^ (i : ℕ)) =
        ∑ i, ((integerCoeffs (E := E) k x i : ℤ) • (b i : coeffRing (E := E) k) : E) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← show ((b i : coeffRing (E := E) k) : E) =
            hawkZeta (E := E) k ^ (i : ℕ) from integralHawkBasis_apply (E := E) k i]
          change ((integerCoeffs (E := E) k x i : ℚ) • ((b i : coeffRing (E := E) k) : E)) =
            (Subring.subtype (coeffRing (E := E) k))
              ((integerCoeffs (E := E) k x i : ℤ) • b i)
          rw [map_zsmul]
          exact Int.cast_smul_eq_zsmul ℚ _ _
    _ = ((∑ i, (integerCoeffs (E := E) k x i : ℤ) • b i :
       coeffRing (E := E) k) : E) := by
         change (∑ i, (Subring.subtype (coeffRing (E := E) k))
             ((integerCoeffs (E := E) k x i : ℤ) • b i)) =
           (Subring.subtype (coeffRing (E := E) k))
             (∑ i, (integerCoeffs (E := E) k x i : ℤ) • b i)
         rw [map_sum]
    _ = x := by
      exact congrArg (fun y : coeffRing (E := E) k => (y : E)) hrepr

/-- Every element of `ℤ[ζ]` has integral rational power-basis coordinates. -/
theorem coeffs_integral (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E]
    (x : E) (hx : x ∈ coeffRing (E := E) k)
    (i : Fin (hawkDegree k)) :
    ∃ z : ℤ, coeffs (E := E) k x i = (z : ℚ) := by
  let y : coeffRing (E := E) k := ⟨x, hx⟩
  refine ⟨integerCoeffs (E := E) k y i, ?_⟩
  have h := integer_coeffExpansion (E := E) k y
  have hrepr := congrArg (coeffs (E := E) k) h
  rw [coeffs_coeffExpansion] at hrepr
  exact (congrFun hrepr i).symm

/-- Membership in `ℤ[ζ]` is characterized exactly by integral power-basis coordinates. -/
theorem mem_coeffRing_iff_coeffs_integral (k : ℕ)
    [IsCyclotomicExtension {hawkConductor k} ℚ E] (x : E) :
    x ∈ coeffRing (E := E) k ↔
      ∀ i : Fin (hawkDegree k), ∃ z : ℤ, coeffs (E := E) k x i = (z : ℚ) := by
  constructor
  · intro hx i
    exact coeffs_integral (E := E) k x hx i
  · intro h
    have hxmem : coeffExpansion (hawkZeta (E := E) k)
        (coeffs (E := E) k x) ∈ coeffRing (E := E) k := by
      change (∑ i, (coeffs (E := E) k x i) •
        hawkZeta (E := E) k ^ (i : ℕ)) ∈ coeffRing (E := E) k
      apply Subring.sum_mem
      intro i hi
      obtain ⟨z, hz⟩ := h i
      rw [hz]
      rw [Algebra.smul_def]
      change (algebraMap ℚ E (z : ℚ)) * hawkZeta (E := E) k ^ (i : ℕ) ∈
        coeffRing (E := E) k
      have hcast : algebraMap ℚ E (z : ℚ) = (z : E) := by simp
      rw [hcast]
      exact (coeffRing (E := E) k).mul_mem
        (intCast_mem (coeffRing (E := E) k) z)
        ((coeffRing (E := E) k).pow_mem (hawkZeta_mem_coeffRing (E := E) k) _)
    simpa only [coeffExpansion_coeffs] using hxmem

end Hawk.IntegralCoefficients
