-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_lt_of_occupation_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:02:37.547299+00:00
-- url     : https://prove2.me/submissions/a94f47d6-7895-41c6-a551-d27b185b5072

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: the conditioned-walk coalescence bridge

Bridges the *stochastic* occupation lower bound (`occupation_unbounded_eta`, applied to the conditioned
walk `Ûmat = Umat/umass`) back to the *substochastic* coalescing mass `umass`.  The conditioned
coalescence recursion is `umass(t+1) ≤ umass(t) − δ·umass(t)·ĝ(t)` where `ĝ(t)` is the conditioned
window fraction; with the conditioned window occupation `∑ ĝ` unbounded, `umass → 0` (any threshold `ε`
is eventually beaten).  Pure real-sequence argument.  Opus-authored.
-/

noncomputable section

open Finset

end

open Finset
theorem solution (u g : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hu_nn : ∀ t, 0 ≤ u t) (hu0 : u 0 ≤ 1) (hg_nn : ∀ t, 0 ≤ g t)
    (hrec : ∀ t, u (t + 1) ≤ u t - δ * (u t * g t))
    (hgunb : ∀ K : ℝ, ∃ M, K ≤ ∑ t ∈ Finset.range M, g t)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M, u M ≤ ε := by
  by_contra hcon
  push_neg at hcon
  -- under the assumption u M > ε for all M, telescope the recursion with u t ≥ ε
  have htel : ∀ M, u M ≤ u 0 - δ * ε * ∑ t ∈ Finset.range M, g t := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, mul_add]
      have h1 := hrec M
      have h2 : ε ≤ u M := le_of_lt (hcon M)
      have h3 : δ * (ε * g M) ≤ δ * (u M * g M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (hg_nn M)) hδ.le
      nlinarith [ih, h1, h3]
  obtain ⟨M, hM⟩ := hgunb (2 / (δ * ε))
  have hd : 0 < δ * ε := mul_pos hδ hε
  have hcancel : δ * ε * (2 / (δ * ε)) = 2 := by field_simp
  have hge : δ * ε * (2 / (δ * ε)) ≤ δ * ε * ∑ t ∈ Finset.range M, g t :=
    mul_le_mul_of_nonneg_left hM hd.le
  rw [hcancel] at hge
  have hfinal : u M ≤ -1 := by linarith [htel M, hu0, hge]
  linarith [hcon M, hfinal, hε]
