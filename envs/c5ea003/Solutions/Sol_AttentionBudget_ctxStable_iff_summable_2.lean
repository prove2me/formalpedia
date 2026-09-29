-- Prove2me | solution 2 for AttentionBudget.ctxStable_iff_summable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T13:29:34.675901+00:00
-- url     : https://prove2.me/submissions/e3a68a00-13c4-40a1-8274-29de2355a9ba

import Mathlib
import Definitions.Def_Shared_AttentionBudgetScaling
import Definitions.Def_Shared_AttentionBudgetSummability

open AttentionBudget Finset Filter in
theorem solution {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ1 : τ < 1) : CtxStable w τ ↔ Summable w := by
  have hnonneg : ∀ k, 0 ≤ headMass w k := fun k => Finset.sum_nonneg fun i _ => (hw i).le
  have hpos : ∀ n, 1 ≤ n → 0 < headMass w n := fun n hn =>
    Finset.sum_pos (fun i _ => hw i) (Finset.nonempty_range_iff.2 (by omega))
  have hmono : Monotone (headMass w) := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) fun i _ _ => (hw i).le
  have hmem : ∀ n, 1 ≤ n → n ∈ {k | τ ≤ retained w n k} := by
    intro n hn
    show τ ≤ headMass w (min n n) / headMass w n
    rw [min_self, div_self (hpos n hn).ne']
    exact hτ1.le
  constructor
  · -- a uniform knee bounds every partial sum by `headMass w K / τ`
    rintro ⟨K, hK⟩
    refine summable_of_sum_range_le (c := headMass w K / τ) (fun i => (hw i).le) fun n => ?_
    show headMass w n ≤ headMass w K / τ
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [headMass, Finset.range_zero, Finset.sum_empty]
      exact div_nonneg (hnonneg K) hτ0.le
    by_cases hnK : n ≤ K
    · exact (hmono hnK).trans (le_div_self (hnonneg K) hτ0 hτ1.le)
    · have hk : kstar w n τ ≤ K := hK n hn
      have hk_mem : τ ≤ retained w n (kstar w n τ) := Nat.sInf_mem ⟨n, hmem n hn⟩
      have hret : retained w n (kstar w n τ) ≤ headMass w K / headMass w n := by
        show headMass w (min (kstar w n τ) n) / headMass w n ≤ headMass w K / headMass w n
        refine div_le_div_of_nonneg_right (hmono ?_) (hpos n hn).le
        exact (min_le_left _ _).trans hk
      have h1 : τ * headMass w n ≤ headMass w K :=
        (le_div_iff₀ (hpos n hn)).1 (hk_mem.trans hret)
      rw [le_div_iff₀ hτ0]
      linarith
  · -- a summable profile clears the gate with a fixed head
    intro hs
    have hS : 0 < ∑' i, w i := hs.tsum_pos (fun i => (hw i).le) 0 (hw 0)
    have hle : ∀ n, headMass w n ≤ ∑' i, w i := fun n =>
      hs.sum_le_tsum (range n) (fun i _ => (hw i).le)
    have hev : ∀ᶠ n in atTop, τ * ∑' i, w i < headMass w n :=
      hs.hasSum.tendsto_sum_nat.eventually (lt_mem_nhds (by nlinarith))
    obtain ⟨K, hKev⟩ := Filter.eventually_atTop.1 hev
    refine ⟨K, fun n hn => ?_⟩
    by_cases hnK : K ≤ n
    · apply Nat.sInf_le
      show τ ≤ headMass w (min K n) / headMass w n
      rw [min_eq_left hnK, le_div_iff₀ (hpos n hn)]
      have := hKev K le_rfl
      nlinarith [hle n]
    · exact (Nat.sInf_le (hmem n hn)).trans (by omega)
