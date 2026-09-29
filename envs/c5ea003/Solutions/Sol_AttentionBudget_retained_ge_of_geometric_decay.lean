-- Prove2me | solution 1 for AttentionBudget.retained_ge_of_geometric_decay
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T20:21:20.02103+00:00
-- url     : https://prove2.me/submissions/96a21da7-1dc0-4f81-bbe0-61d7ecd422ad

-- Sol generated from Shared/AttentionBudgetKnee.lean
import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee
import Theorems.Thm_AttentionBudget_headMass_mono
import Theorems.Thm_AttentionBudget_headMass_pos
import Theorems.Thm_AttentionBudget_tail_le_geometric

open AttentionBudget
open Finset

variable {w : ℕ → ℝ} (hw : ∀ i, 0 < w i)
include hw
variable {w : ℕ → ℝ} {τ : ℝ} {n : ℕ} (hw : ∀ i, 0 < w i)
include hw
variable {w : ℕ → ℝ} {r τ : ℝ}

open AttentionBudget in
theorem solution (hw : ∀ i, 0 < w i) (hr0 : 0 < r) (hr1 : r < 1)
    (hdec : ∀ i, w (i + 1) ≤ r * w i) {n k : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    1 - r ^ k / (1 - r) ≤ retained w n k := by
  have hr1' : (0 : ℝ) < 1 - r := by linarith
  have hw0 : 0 < w 0 := hw 0
  have ht : (0 : ℝ) ≤ r ^ k / (1 - r) := div_nonneg (pow_nonneg hr0.le k) hr1'.le
  rcases le_or_gt n k with hnk | hkn
  · rw [retained, min_eq_right hnk, div_self (headMass_pos hw hn).ne']
    linarith
  · have hmin : min k n = k := min_eq_left hkn.le
    have hA : w 0 ≤ headMass w k := by
      have : headMass w 1 ≤ headMass w k := headMass_mono hw hk
      simpa [headMass] using this
    have hAB : headMass w k ≤ headMass w n := headMass_mono hw hkn.le
    have hB : 0 < headMass w n := headMass_pos hw hn
    have htail : headMass w n - headMass w k ≤ w 0 * (r ^ k / (1 - r)) := by
      have := tail_le_geometric hw hr0 hr1 hdec hw k n
      rw [mul_div_assoc] at this
      exact this
    rw [retained, hmin, le_div_iff₀ hB]
    nlinarith [mul_le_mul_of_nonneg_left hA ht]
