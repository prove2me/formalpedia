-- Prove2me | solution 1 for AttentionBudget.not_ctxStable_uniform
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T20:23:56.420284+00:00
-- url     : https://prove2.me/submissions/ca4787fc-217d-4ef2-8ba5-482f6d18f459

-- Sol generated from Shared/AttentionBudgetScaling.lean
import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee
import Definitions.Def_Shared_AttentionBudgetScaling
import Theorems.Thm_AttentionBudget_kstar_uniform_ge

open AttentionBudget
open Finset

lemma uniform_pos : ∀ i : ℕ, (0 : ℝ) < (fun _ => (1 : ℝ)) i := fun _ => one_pos

variable {w₁ w₂ : ℕ → ℝ} {τ : ℝ} {n : ℕ}

open AttentionBudget in
theorem solution {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1) :
    ¬ CtxStable (fun _ => (1 : ℝ)) τ := by
  rintro ⟨K, hK⟩
  obtain ⟨m, hm⟩ := exists_nat_gt ((K + 1 : ℝ) / τ)
  set n := max m 1 with hn
  have hn0 : 0 < n := by omega
  have hnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_left m 1
  have hbig : (K : ℝ) + 1 ≤ τ * n := by
    rw [div_lt_iff₀ hτ0] at hm
    nlinarith
  have hlow := @kstar_uniform_ge (fun _ => (1 : ℝ)) uniform_pos τ n hn0 hτ
  have hup : (kstar (fun _ => (1 : ℝ)) n τ : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hK n hn0
  linarith
