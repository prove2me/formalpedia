-- Prove2me | solution 1 for ReweightedNPMLE.sum_abs_simplexGridRound_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:04:40.272817+00:00
-- url     : https://prove2.me/submissions/a88b6319-c978-486f-a897-3a42c1ef3b73

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





theorem nonnegativeGridFloor_le {M : ℕ} (hM : 0 < M)
    {x : ℝ} (hx : 0 ≤ x) :
    nonnegativeGridFloor M x ≤ x := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  rw [nonnegativeGridFloor, div_le_iff₀ hMreal]
  simpa only [mul_comm] using Nat.floor_le (mul_nonneg hMreal.le hx)

theorem sub_nonnegativeGridFloor_lt {M : ℕ} (hM : 0 < M)
    (x : ℝ) :
    x - nonnegativeGridFloor M x < 1 / M := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  rw [sub_lt_iff_lt_add]
  calc
    x = ((M : ℝ) * x) / M := by field_simp
    _ < ((⌊(M : ℝ) * x⌋₊ : ℝ) + 1) / M :=
      div_lt_div_of_pos_right (Nat.lt_floor_add_one ((M : ℝ) * x)) hMreal
    _ = 1 / M + nonnegativeGridFloor M x := by
      rw [nonnegativeGridFloor, add_div]
      ring



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
/-- The denominator-grid rounding error in `ℓ¹` is at most `2k/M` for a
simplex with `k+1` slots. -/
theorem solution {k M : ℕ} (hM : 0 < M)
    (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1) :
    ∑ i, |simplexGridRound k M w i - w i| ≤
      2 * k / M := by
  let last := Fin.last k
  let E := ∑ i ∈ Finset.univ.erase last,
    (w i - nonnegativeGridFloor M (w i))
  have herr_nonneg (i : Fin (k + 1)) :
      0 ≤ w i - nonnegativeGridFloor M (w i) :=
    sub_nonneg.mpr (nonnegativeGridFloor_le hM (hw i))
  have hlast : simplexGridRound k M w last - w last = E := by
    have hdecomp :
        (∑ i ∈ Finset.univ.erase last, w i) + w last = 1 := by
      calc
        (∑ i ∈ Finset.univ.erase last, w i) + w last =
            ∑ i ∈ (Finset.univ : Finset (Fin (k + 1))), w i :=
          Finset.sum_erase_add Finset.univ w (Finset.mem_univ last)
        _ = 1 := by simpa using hwsum
    rw [show simplexGridRound k M w last =
        1 - ∑ i ∈ Finset.univ.erase last,
          nonnegativeGridFloor M (w i) by
      simp only [last, simplexGridRound_apply_last]]
    dsimp only [E]
    rw [Finset.sum_sub_distrib]
    linarith
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact Finset.sum_nonneg fun i _ ↦ herr_nonneg i
  have hl1eq :
      (∑ i, |simplexGridRound k M w i - w i|) = 2 * E := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ last)]
    have herase :
        (∑ i ∈ Finset.univ.erase last,
          |simplexGridRound k M w i - w i|) = E := by
      dsimp only [E]
      apply Finset.sum_congr rfl
      intro i hi
      rw [simplexGridRound_apply_of_ne w (Finset.ne_of_mem_erase hi)]
      rw [abs_sub_comm, abs_of_nonneg (herr_nonneg i)]
    rw [herase, hlast, abs_of_nonneg hE]
    ring
  rw [hl1eq]
  have hEbound : E ≤ k * (1 / (M : ℝ)) := by
    dsimp only [E]
    calc
      (∑ i ∈ Finset.univ.erase last,
          (w i - nonnegativeGridFloor M (w i))) ≤
          ∑ _i ∈ Finset.univ.erase last, (1 / (M : ℝ)) := by
        apply Finset.sum_le_sum
        intro i _
        exact (sub_nonnegativeGridFloor_lt hM (w i)).le
      _ = k * (1 / (M : ℝ)) := by simp [last]
  calc
    2 * E ≤ 2 * (k * (1 / (M : ℝ))) :=
      mul_le_mul_of_nonneg_left hEbound (by norm_num)
    _ = 2 * k / M := by ring
