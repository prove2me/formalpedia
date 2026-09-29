-- Prove2me | solution 1 for TropicalLA.no_spread_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T09:55:23.768357+00:00
-- url     : https://prove2.me/submissions/08313c65-8b31-4907-bad7-0d44f4a3f933

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCyclicity
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalGelfand
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius

open Finset TropicalLA in
theorem solution :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ),
      IsTropEigen A (maxCycleMean A) v ∧ spread v = 0 ∧
      ∀ (m : ℕ) (i : Fin 2), tpow A m i 1 ≤ ((m : ℝ) + 1) * maxCycleMean A - 3 := by
  refine ⟨fun _ j => if j = 0 then 0 else -3, fun _ => 0, ?_⟩
  set A : Matrix (Fin 2) (Fin 2) ℝ := fun _ j => if j = 0 then 0 else -3 with hA
  have hA0 : ∀ i, A i 0 = 0 := fun i => by simp [hA]
  have hA1 : ∀ i, A i 1 = -3 := fun i => by simp [hA]
  have hAle : ∀ i j, A i j ≤ 0 := by
    intro i j
    by_cases hj : j = 0 <;> norm_num [hA, hj]
  have hstep : ∀ m i t, tpow A (m + 1) i t
      = univ.sup' univ_nonempty (fun l => tpow A m i l + A l t) := fun _ _ _ => rfl
  have hle0 : ∀ m i j, tpow A m i j ≤ 0 := by
    intro m
    induction m with
    | zero =>
      intro i j
      exact hAle i j
    | succ m ih =>
      intro i j
      rw [hstep]
      apply Finset.sup'_le
      intro l _
      linarith [ih i l, hAle l j]
  have hmcm : maxCycleMean A = 0 := by
    apply le_antisymm
    · unfold maxCycleMean
      apply Finset.sup'_le
      rintro ⟨k, i⟩ _
      dsimp only
      exact div_nonpos_of_nonpos_of_nonneg (hle0 k i i) (by positivity)
    · unfold maxCycleMean
      refine le_trans ?_ (Finset.le_sup' (fun q : ℕ × Fin 2 => tpow A q.1 q.2 q.2 / ((q.1 : ℝ) + 1))
        (show ((0 : ℕ), (0 : Fin 2)) ∈ range (Fintype.card (Fin 2)) ×ˢ (univ : Finset (Fin 2)) by
          simp))
      show (0 : ℝ) ≤ tpow A 0 0 0 / (((0 : ℕ) : ℝ) + 1)
      rw [show tpow A 0 0 0 = A 0 0 from rfl, hA0 0]
      simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hmcm]
    intro i
    show univ.sup' univ_nonempty (fun j => A i j + (0 : ℝ)) = 0 + 0
    apply le_antisymm
    · apply Finset.sup'_le
      intro j _
      linarith [hAle i j]
    · refine le_trans ?_ (Finset.le_sup' (fun j => A i j + (0 : ℝ)) (mem_univ 0))
      simp [hA0]
  · simp [spread, Finset.sup'_const, Finset.inf'_const]
  · intro m i
    rw [hmcm]
    rcases m with _ | m
    · show A i 1 ≤ _
      rw [hA1 i]
      norm_num
    · rw [hstep]
      apply Finset.sup'_le
      intro l _
      have := hle0 m i l
      rw [hA1 l]
      linarith
