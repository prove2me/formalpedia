-- Prove2me | solution 1 for ReweightedNPMLE.simplexGridRound_mem_simplexWeightGrid
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:04:28.184932+00:00
-- url     : https://prove2.me/submissions/370aa725-5e7c-4dcc-90a9-f1f61fc1da7a

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights

-- Inline helpers preserved from ReweightedNPMLE.SimplexGrid.
section
/-!
# Finite simplex-grid rounding

The deterministic denominator-grid construction used to discretize the
Carathéodory mixture weights in the likelihood net.
-/

open scoped BigOperators

namespace ReweightedNPMLE











theorem simplexGridRound_apply_of_ne {k M : ℕ}
    (w : Fin (k + 1) → ℝ) {i : Fin (k + 1)} (hi : i ≠ Fin.last k) :
    simplexGridRound k M w i = nonnegativeGridFloor M (w i) := by
  simp [simplexGridRound, hi]

@[simp]
theorem simplexGridRound_apply_last {k M : ℕ}
    (w : Fin (k + 1) → ℝ) :
    simplexGridRound k M w (Fin.last k) =
      1 - ∑ j ∈ (Finset.univ.erase (Fin.last k)),
        nonnegativeGridFloor M (w j) := by
  simp [simplexGridRound]







/-- A simplex coordinate is at most one. -/
theorem simplex_coordinate_le_one {k : ℕ} (w : Fin (k + 1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (i : Fin (k + 1)) :
    w i ≤ 1 := by
  calc
    w i ≤ ∑ j, w j :=
      Finset.single_le_sum (fun j _ ↦ hw j) (Finset.mem_univ i)
    _ = 1 := hwsum

/-- The integer numerator obtained by rounding a simplex coordinate down is
bounded by the grid denominator. -/
theorem nonnegativeGridNumerator_le {M : ℕ} {x : ℝ}
    (hx1 : x ≤ 1) :
    ⌊(M : ℝ) * x⌋₊ ≤ M := by
  apply Nat.floor_le_of_le
  exact mul_le_of_le_one_right (Nat.cast_nonneg M) hx1

/-- Delete the last coordinate from a finite sum. -/
theorem sum_erase_last_eq_sum_castSucc {k : ℕ} (f : Fin (k + 1) → ℝ) :
    ∑ i ∈ Finset.univ.erase (Fin.last k), f i =
      ∑ i : Fin k, f i.castSucc := by
  have herase := Finset.sum_erase_add
    (Finset.univ : Finset (Fin (k + 1))) f (Finset.mem_univ (Fin.last k))
  rw [Fin.sum_univ_castSucc] at herase
  exact add_right_cancel herase























end ReweightedNPMLE
end

/-!
# Finite simplex-grid rounding

The deterministic denominator-grid construction used to discretize the
Carathéodory mixture weights in the likelihood net.
-/

open scoped BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Rounding a simplex vector produces a member of the finite weight grid. -/
theorem solution {k M : ℕ}
    (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1) :
    simplexGridRound k M w ∈ simplexWeightGrid k M := by
  let a : Fin k → Fin (M + 1) := fun i ↦
    ⟨⌊(M : ℝ) * w i.castSucc⌋₊,
      Nat.lt_succ_of_le (nonnegativeGridNumerator_le
        (simplex_coordinate_le_one w hw hwsum i.castSucc))⟩
  rw [simplexWeightGrid, Finset.mem_image]
  refine ⟨a, Finset.mem_univ a, ?_⟩
  funext i
  cases i using Fin.lastCases with
  | last =>
      rw [simplexGridRound_apply_last, simplexGridPoint]
      simp only [Fin.snoc_last]
      congr 1
      rw [sum_erase_last_eq_sum_castSucc]
      simp only [a, nonnegativeGridFloor]
  | cast i =>
      rw [simplexGridRound_apply_of_ne w (Fin.castSucc_ne_last i),
        simplexGridPoint]
      simp only [Fin.snoc_castSucc, a, nonnegativeGridFloor]
