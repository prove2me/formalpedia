-- Prove2me | solution 1 for AttentionBudget.kstar_uniformly_bounded_of_geometric_decay
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T20:23:55.610398+00:00
-- url     : https://prove2.me/submissions/c4fe553d-8e79-4581-a98c-ffb68654f63c

-- Sol generated from Shared/AttentionBudgetKnee.lean
import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee
import Theorems.Thm_AttentionBudget_kstar_le_of_pass
import Theorems.Thm_AttentionBudget_retained_ge_of_geometric_decay

open AttentionBudget
open Finset

variable {w : ℕ → ℝ} (hw : ∀ i, 0 < w i)
include hw
variable {w : ℕ → ℝ} {τ : ℝ} {n : ℕ} (hw : ∀ i, 0 < w i)
include hw
variable {w : ℕ → ℝ} {r τ : ℝ}

open AttentionBudget in
theorem solution (hw : ∀ i, 0 < w i) (hr0 : 0 < r)
    (hr1 : r < 1) (hdec : ∀ i, w (i + 1) ≤ r * w i) (hτ : τ < 1) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → kstar w n τ ≤ K := by
  have hr1' : (0 : ℝ) < 1 - r := by linarith
  obtain ⟨K0, hK0⟩ : ∃ m : ℕ, r ^ m < (1 - τ) * (1 - r) :=
    exists_pow_lt_of_lt_one (by nlinarith) hr1
  refine ⟨max K0 1, le_max_right _ _, fun n hn => ?_⟩
  have hpow : r ^ (max K0 1) ≤ r ^ K0 :=
    pow_le_pow_of_le_one hr0.le hr1.le (le_max_left _ _)
  have hgate : τ ≤ 1 - r ^ (max K0 1) / (1 - r) := by
    rw [le_sub_iff_add_le, ← sub_nonneg]
    have : r ^ (max K0 1) / (1 - r) < 1 - τ := by
      rw [div_lt_iff₀ hr1']
      linarith
    linarith
  exact kstar_le_of_pass
    (hgate.trans (retained_ge_of_geometric_decay hw hw hr0 hr1 hdec (le_max_right _ _) hn))
