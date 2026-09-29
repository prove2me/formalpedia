-- Prove2me | solution 1 for AttentionBudget.kstar_uniform_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T20:17:38.537883+00:00
-- url     : https://prove2.me/submissions/5ef507c0-d07b-47c0-8b0d-aa5c9d5e290d

-- Sol generated from Shared/AttentionBudgetKnee.lean
import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee
import Theorems.Thm_AttentionBudget_kstar_ge_of_bounded_ratio

open AttentionBudget
open Finset

lemma uniform_pos : ∀ i : ℕ, (0 : ℝ) < (fun _ => (1 : ℝ)) i := fun _ => one_pos

variable {w : ℕ → ℝ} (hw : ∀ i, 0 < w i)
include hw
variable {w : ℕ → ℝ} {τ : ℝ} {n : ℕ} (hw : ∀ i, 0 < w i)
include hw
variable {w : ℕ → ℝ} {r τ : ℝ}
variable {w : ℕ → ℝ} {τ : ℝ} {n : ℕ}

open AttentionBudget in
theorem solution (hn : 0 < n) (hτ : τ ≤ 1) :
    τ * n ≤ (kstar (fun _ => (1 : ℝ)) n τ : ℝ) := by
  have := @kstar_ge_of_bounded_ratio (fun _ => (1 : ℝ)) uniform_pos (fun _ => (1 : ℝ)) τ n
    uniform_pos (1 : ℝ) 1 one_pos (fun _ => le_rfl) (fun _ => le_rfl) hn hτ
  simpa using this
