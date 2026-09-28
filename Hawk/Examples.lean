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
  fin_cases i <;> norm_num [signature, preimage, B, h, x, mulVec, dotProduct,
    Fin.sum_univ_two]

example : h - signature B h x = ![0, 1] := by
  ext i
  fin_cases i <;> norm_num [signature, preimage, B, h, x, mulVec, dotProduct,
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

end Hawk.Examples
