-- Prove2me | solution 1 for ReweightedNPMLE.simplexGridRound_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:04:34.651631+00:00
-- url     : https://prove2.me/submissions/aef8ecce-8b7f-4c80-82ae-63d3c635244a

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



theorem nonnegativeGridFloor_nonneg (M : ℕ) (x : ℝ) :
    0 ≤ nonnegativeGridFloor M x := by
  unfold nonnegativeGridFloor
  positivity

theorem nonnegativeGridFloor_le {M : ℕ} (hM : 0 < M)
    {x : ℝ} (hx : 0 ≤ x) :
    nonnegativeGridFloor M x ≤ x := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  rw [nonnegativeGridFloor, div_le_iff₀ hMreal]
  simpa only [mul_comm] using Nat.floor_le (mul_nonneg hMreal.le hx)





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
theorem solution {k M : ℕ} (hM : 0 < M)
    (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1) (i : Fin (k + 1)) :
    0 ≤ simplexGridRound k M w i := by
  by_cases hi : i = Fin.last k
  · subst i
    rw [simplexGridRound_apply_last]
    have hroundsum :
        ∑ j ∈ Finset.univ.erase (Fin.last k), nonnegativeGridFloor M (w j) ≤
          ∑ j ∈ Finset.univ.erase (Fin.last k), w j := by
      apply Finset.sum_le_sum
      intro j _
      exact nonnegativeGridFloor_le hM (hw j)
    have hdecomp :
        (∑ j ∈ Finset.univ.erase (Fin.last k), w j) + w (Fin.last k) = 1 := by
      calc
        (∑ j ∈ Finset.univ.erase (Fin.last k), w j) + w (Fin.last k) =
            ∑ j ∈ (Finset.univ : Finset (Fin (k + 1))), w j :=
          Finset.sum_erase_add Finset.univ w (Finset.mem_univ (Fin.last k))
        _ = 1 := by simpa using hwsum
    have hsum_le_one :
        (∑ j ∈ Finset.univ.erase (Fin.last k), w j) ≤ 1 := by
      linarith [hw (Fin.last k)]
    exact sub_nonneg.mpr (hroundsum.trans hsum_le_one)
  · rw [simplexGridRound_apply_of_ne w hi]
    exact nonnegativeGridFloor_nonneg M (w i)
