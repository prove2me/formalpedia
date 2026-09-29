-- Prove2me | solution 2 for AttentionBudget.kstar_ge_of_bounded_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T19:54:27.893985+00:00
-- url     : https://prove2.me/submissions/4cbf094d-61d9-4fd5-b947-1f7230aa1d63

import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee
open AttentionBudget Finset in
theorem solution {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) {w : ℕ → ℝ} {τ : ℝ} {n : ℕ}
    (hw : ∀ i, 0 < w i) {c M : ℝ} (hc : 0 < c)
    (hlow : ∀ i, c ≤ w i) (hhigh : ∀ i, w i ≤ M) (hn : 0 < n) (hτ : τ ≤ 1) :
    τ * n * c / M ≤ (kstar w n τ : ℝ) := by
  have hM : 0 < M := lt_of_lt_of_le (hw 0) (hhigh 0)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- the full window carries at least `n c`, any window of `k` keys at most `k M`
  have hHn : (n : ℝ) * c ≤ headMass w n := by
    unfold headMass
    have := sum_le_sum (fun i (_ : i ∈ range n) => hlow i)
    rw [sum_const, card_range, nsmul_eq_mul] at this
    exact this
  have hHpos : 0 < headMass w n := lt_of_lt_of_le (mul_pos hn' hc) hHn
  have hHk : ∀ k : ℕ, headMass w (min k n) ≤ k * M := by
    intro k
    unfold headMass
    calc ∑ i ∈ range (min k n), w i ≤ ∑ i ∈ range (min k n), M :=
          sum_le_sum (fun i _ => hhigh i)
      _ = ((min k n : ℕ) : ℝ) * M := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ k * M := mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_left k n) hM.le
  -- the knee exists (the full context passes) and passes the gate
  have hne : n ∈ {k | τ ≤ retained w n k} := by
    show τ ≤ retained w n n
    unfold retained
    rw [min_self, div_self hHpos.ne']
    exact hτ
  have hks : τ ≤ retained w n (kstar w n τ) := Nat.sInf_mem ⟨n, hne⟩
  unfold retained at hks
  rw [le_div_iff₀ hHpos] at hks
  have hk := hHk (kstar w n τ)
  rw [div_le_iff₀ hM]
  rcases le_total 0 τ with hτ0 | hτ0
  · have := mul_le_mul_of_nonneg_left hHn hτ0
    nlinarith
  · have h1 : τ * n * c ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hτ0 hn'.le) hc.le
    have h2 : 0 ≤ (kstar w n τ : ℝ) * M := mul_nonneg (Nat.cast_nonneg _) hM.le
    linarith
