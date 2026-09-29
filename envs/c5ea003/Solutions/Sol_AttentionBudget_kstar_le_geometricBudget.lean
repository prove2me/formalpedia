-- Prove2me | solution 1 for AttentionBudget.kstar_le_geometricBudget
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T20:23:55.036026+00:00
-- url     : https://prove2.me/submissions/c957ceac-2596-4f0e-af48-36ce22d3f703

-- Sol generated from Shared/AttentionBudgetScaling.lean
import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee
import Definitions.Def_Shared_AttentionBudgetScaling
import Theorems.Thm_AttentionBudget_kstar_le_of_pass
import Theorems.Thm_AttentionBudget_retained_ge_of_geometric_decay

open AttentionBudget
open Finset

open AttentionBudget in
theorem solution {w : ℕ → ℝ} {r τ : ℝ} (hw : ∀ i, 0 < w i) (hr0 : 0 < r)
    (hr1 : r < 1) (hdec : ∀ i, w (i + 1) ≤ r * w i) (hτ : τ < 1) {n : ℕ} (hn : 1 ≤ n) :
    kstar w n τ ≤ geometricBudget r τ := by
  set K := geometricBudget r τ with hKdef
  have hr1' : (0 : ℝ) < 1 - r := by linarith
  have hc : 0 < (1 - τ) * (1 - r) := mul_pos (by linarith) hr1'
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  have hKge : Real.log ((1 - τ) * (1 - r)) / Real.log r ≤ (K : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    have : (⌈Real.log ((1 - τ) * (1 - r)) / Real.log r⌉₊ : ℕ) ≤ K := le_max_left _ _
    exact_mod_cast this
  have hmul : (K : ℝ) * Real.log r ≤ Real.log ((1 - τ) * (1 - r)) := by
    rwa [div_le_iff_of_neg hlogr] at hKge
  have hpow : r ^ K ≤ (1 - τ) * (1 - r) := by
    have hlp : Real.log (r ^ K) = (K : ℝ) * Real.log r := by rw [Real.log_pow]
    exact (Real.log_le_log_iff (pow_pos hr0 K) hc).mp (by rw [hlp]; exact hmul)
  have hK1 : 1 ≤ K := le_max_right _ _
  have hdivle : r ^ K / (1 - r) ≤ 1 - τ := by
    rw [div_le_iff₀ hr1']
    linarith
  exact kstar_le_of_pass
    (le_trans (by linarith) (retained_ge_of_geometric_decay hw hw hr0 hr1 hdec hK1 hn))
