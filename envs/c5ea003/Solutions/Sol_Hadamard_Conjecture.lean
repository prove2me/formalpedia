-- Prove2me | solution 1 for Hadamard_Conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T04:06:08.011245+00:00
-- url     : https://prove2.me/submissions/6d38d320-a91c-4126-acdb-1267ec40d9a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Hadamard_tensor_product_exists
import Theorems.Thm_Hadamard_odd_multiplier_exists
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

theorem solution (k : ℕ) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by
  have htwo : ∀ i j, (!![(1 : ℝ), 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ) i j ∈
      ({1, -1} : Finset ℝ) := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hdet : |(!![(1 : ℝ), 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ).det| =
      (2 : ℝ) ^ ((2 : ℝ) / 2) := by
    norm_num [Matrix.det_fin_two]
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · subst k
      refine ⟨0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp
    rcases Nat.even_or_odd k with he | ho
    · obtain ⟨t, rfl⟩ := he
      obtain ⟨A, hA, hdA⟩ := ih t (by omega)
      have hsize : 2 * (4 * t) = 4 * (t + t) := by omega
      exact hsize ▸
        (Hadamard.tensor_product_exists 2 (4 * t) !![(1 : ℝ), 1; 1, -1] A
          htwo hA hdet hdA)
    · exact Hadamard.odd_multiplier_exists k ho
