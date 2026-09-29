-- Prove2me | solution 2 for AttentionBudget.kstar_uniform_ge
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-19T16:45:06.962935+00:00
-- url     : https://prove2.me/submissions/08a766f3-bd2f-4a56-90d1-da72ffbe6fb7

import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee

open AttentionBudget Finset

private theorem headMass_one (k : ℕ) :
    headMass (fun _ => (1 : ℝ)) k = (k : ℝ) := by
  simp [headMass, sum_const, card_range, nsmul_eq_mul]

private theorem retained_one (n k : ℕ) :
    retained (fun _ => (1 : ℝ)) n k = (min k n : ℝ) / n := by
  simp [retained, headMass_one]

/-- Matches the elaborated type of `kstar_uniform_ge` (ambient `w`/`hw` from the Knee section). -/
theorem solution {w : ℕ → ℝ} (_hw : ∀ i, 0 < w i) {τ : ℝ} {n : ℕ}
    (hn : 0 < n) (hτ : τ ≤ 1) :
    τ * n ≤ (kstar (fun _ => (1 : ℝ)) n τ : ℝ) := by
  classical
  set W : ℕ → ℝ := fun _ => (1 : ℝ)
  set S : Set ℕ := {k | τ ≤ retained W n k}
  have h1 : retained W n n = 1 := by
    rw [retained_one n n, min_self]; field_simp
  have hne : S.Nonempty := ⟨n, by change τ ≤ retained W n n; simpa [h1] using hτ⟩
  have hmem : τ ≤ retained W n (kstar W n τ) := by
    have : kstar W n τ ∈ S := by simpa [kstar, S] using Nat.sInf_mem hne
    exact this
  have hle : retained W n (kstar W n τ) ≤ (kstar W n τ : ℝ) / n := by
    rw [retained_one n _]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
    exact_mod_cast min_le_left _ _
  have hdiv : τ ≤ (kstar W n τ : ℝ) / n := le_trans hmem hle
  exact (le_div_iff₀ (Nat.cast_pos.mpr hn)).1 hdiv
