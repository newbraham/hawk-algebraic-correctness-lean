import Mathlib.Tactic.FinCases
import Hawk.Signing

/-! Exact rational examples, not substitutes for the universal proofs. -/
noncomputable section
open scoped Matrix
open Matrix
namespace Hawk.Examples

def B : (Matrix (Fin 2) (Fin 2) ℚ)ˣ where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

def h : Fin 2 → ℚ := ![1, 0]
def z : Fin 2 → ℚ := ![0, 1]
def x : Fin 2 → ℚ := ![1, 2]

example : x = (↑B : Matrix (Fin 2) (Fin 2) ℚ) *ᵥ h + (2 : ℚ) • z := by
  ext i
  fin_cases i <;> norm_num [x, B, h, z, mulVec, dotProduct, Fin.sum_univ_two]

example : preimage B x = ![-1, 2] := by
  ext i
  fin_cases i <;> norm_num [preimage, B, x, mulVec, dotProduct, Fin.sum_univ_two]

example : signature B h x = ![1, -1] := by
  ext i
  fin_cases i <;> norm_num [signature, signatureMod, preimage, B, h, x, mulVec, dotProduct,
    Fin.sum_univ_two]

example : h - signature B h x = ![0, 1] := by
  ext i
  fin_cases i <;> norm_num [signature, signatureMod, preimage, B, h, x, mulVec, dotProduct,
    Fin.sum_univ_two]

example : (↑B : Matrix (Fin 2) (Fin 2) ℚ)ᴴ * (↑B : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 1; 1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [B, conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]

example : traceSq x = 5 := by
  norm_num [traceSq, normalizedTrace, x, dotProduct, Fin.sum_univ_two]

example : publicSq (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ) ![-1, 2] = 5 := by
  norm_num [publicSq, normalizedTrace, mulVec, dotProduct, Fin.sum_univ_two]

example : publicSq (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ) ![1, -2] = 5 := by
  norm_num [publicSq, normalizedTrace, mulVec, dotProduct, Fin.sum_univ_two]

/-- The actual image of ℤ in ℚ, not an unrestricted rational coefficient ring. -/
def integerSubring : Subring ℚ := (Int.castRingHom ℚ).range

/-- With B = 1 and h = x = 1, the modulus-three signature is integral but
its sign-flipped candidate is 2/3. All basis and coset hypotheses hold and
the public metric is still preserved: the obstruction is integrality. -/
theorem modulus_three_counterexample :
    let B : (Matrix (Fin 1) (Fin 1) ℚ)ˣ := 1
    let h : Fin 1 → ℚ := fun _ => 1
    IntegralMat integerSubring (↑B : Matrix (Fin 1) (Fin 1) ℚ) ∧
    IntegralMat integerSubring (↑(B⁻¹) : Matrix (Fin 1) (Fin 1) ℚ) ∧
    IntegralVec integerSubring h ∧
    InSigningCosetMod 3 integerSubring (↑B : Matrix (Fin 1) (Fin 1) ℚ) h h ∧
    IntegralVec integerSubring (signatureMod 3 B h h) ∧
    signatureMod 3 B h h = 0 ∧
    flippedSignatureMod 3 B h h = (fun _ => (2 : ℚ) / 3) ∧
    ¬ IntegralVec integerSubring (flippedSignatureMod 3 B h h) ∧
    ¬ DivisibleVec integerSubring 3 ((2 : ℚ) • h) ∧
    publicSq 1 (h - (3 : ℚ) • flippedSignatureMod 3 B h h) = traceSq h := by
  dsimp only
  let B : (Matrix (Fin 1) (Fin 1) ℚ)ˣ := 1
  let h : Fin 1 → ℚ := fun _ => 1
  have hB : IntegralMat integerSubring (↑B : Matrix (Fin 1) (Fin 1) ℚ) := by
    intro i j
    change (1 : Matrix (Fin 1) (Fin 1) ℚ) i j ∈ integerSubring
    simp only [Matrix.one_apply]
    split_ifs
    · exact integerSubring.one_mem
    · exact integerSubring.zero_mem
  have hBinv : IntegralMat integerSubring (↑(B⁻¹) : Matrix (Fin 1) (Fin 1) ℚ) := by
    simpa [B] using hB
  have hh : IntegralVec integerSubring h := fun _ => integerSubring.one_mem
  have hx : InSigningCosetMod 3 integerSubring (↑B : Matrix (Fin 1) (Fin 1) ℚ) h h := by
    refine ⟨0, (fun _ => integerSubring.zero_mem), ?_⟩
    simp [B]
  have hs := signature_integral_mod 3 (by decide) integerSubring B hBinv h h hx
  have hzero : signatureMod 3 B h h = 0 := by
    ext i
    simp [signatureMod, preimage, B]
  have hflip : flippedSignatureMod 3 B h h = (fun _ => (2 : ℚ) / 3) := by
    ext i
    norm_num [flippedSignatureMod, preimage, B, h]
  have hnot : ¬ IntegralVec integerSubring (flippedSignatureMod 3 B h h) := by
    rw [hflip]
    intro hint
    obtain ⟨z, hz⟩ := hint 0
    change (z : ℚ) = (2 : ℚ) / 3 at hz
    have hden := congrArg Rat.den hz
    norm_num at hden
  refine ⟨hB, hBinv, hh, hx, hs, hzero, hflip, hnot, ?_, ?_⟩
  · intro hdiv
    exact hnot ((flipped_signature_integral_iff 3 (by decide)
      integerSubring B hBinv h h hx).2 hdiv)
  · change publicSq (1 : Matrix (Fin 1) (Fin 1) ℚ)
      (h - (3 : ℚ) • flippedSignatureMod 3 B h h) = traceSq h
    have hrec : h - (3 : ℚ) • flippedSignatureMod 3 B h h = -preimage B h := by
      simpa only [Nat.cast_ofNat] using reconstruction_sign_mod 3 (by decide) B h h
    rw [hrec, publicSq_neg]
    simp [publicSq, traceSq, preimage, B]

end Hawk.Examples
