-- Prove2me | solution 1 for ReweightedNPMLE.sum_simplexGridRound
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:04:59.16079+00:00
-- url     : https://prove2.me/submissions/52d6dcdb-d6fc-46fd-8776-53a8e735238c

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
theorem solution {k M : ℕ} (w : Fin (k + 1) → ℝ) :
    ∑ i, simplexGridRound k M w i = 1 := by
  let last := Fin.last k
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ last)]
  have hsum :
      (∑ i ∈ Finset.univ.erase last, simplexGridRound k M w i) =
        ∑ i ∈ Finset.univ.erase last, nonnegativeGridFloor M (w i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact simplexGridRound_apply_of_ne w (Finset.ne_of_mem_erase hi)
  rw [hsum]
  simp only [last, simplexGridRound_apply_last]
  ring
