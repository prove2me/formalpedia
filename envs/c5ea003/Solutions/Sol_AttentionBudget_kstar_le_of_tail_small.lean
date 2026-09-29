-- Prove2me | solution 1 for AttentionBudget.kstar_le_of_tail_small
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:06:54.327567+00:00
-- url     : https://prove2.me/submissions/03df20bf-9a41-4ea4-bc0f-85572eba8967

-- Sol generated from Shared/AttentionBudgetSummability.lean
import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee
import Definitions.Def_Shared_AttentionBudgetScaling
import Definitions.Def_Shared_AttentionBudgetSummability
import Theorems.Thm_AttentionBudget_headMass_mono
import Theorems.Thm_AttentionBudget_headMass_pos
import Theorems.Thm_AttentionBudget_kstar_le_of_pass

/-!
# The summability criterion: context stability is exactly convergence of the attention
profile

Cycle 3.  Cycles 1–2 exhibited two regimes — geometric decay (context-stable budget)
and a flat band (budget growing linearly with the context).  Geometric decay is however
far from necessary, and the true boundary is identified here.

**Main theorem** (`ctxStable_iff_summable`).  For a positive sorted attention profile
`w` and an interior gate `0 < τ < 1`,

    CtxStable w τ  ↔  Summable w.

Neither the gate nor the model enters: a finite key budget serves *every* context length
precisely when the sorted attention weights form a convergent series.  This upgrades the
sufficient condition of cycle 1 (geometric decay) to a characterisation, and it makes
the observed dichotomy gate-independent — an unexpected rigidity, since one would expect
a harsher gate to shrink the class of stable models.

**Phase transition** (`zipf_phase_transition`).  On the Zipf family
`w i = 1 / (i+1)^s` the criterion becomes `1 < s`: the attention budget undergoes a
sharp phase transition at Zipf exponent `1`, with a bounded budget above it and a budget
diverging with the context below it.  Measuring the knee at two context lengths
therefore locates a model on either side of `s = 1`.

-- !-- Lab Notes -- !--
Hypothesizer (cycle 3):
 (H9)  Geometric decay is not necessary; the true criterion is convergence of the
       profile.                                                              [BOLD]
 (H10) The criterion is independent of the gate `τ ∈ (0,1)`: stability is a
       property of the profile, not of the measurement bar.                  [BOLD]
 (H11) On Zipf profiles there is a critical exponent, and it is exactly `1`.

Experimenter: H9 and H10 are the two directions of `ctxStable_iff_summable` (the
statement quantifies over an arbitrary interior gate, so gate-independence is a
corollary, recorded as `ctxStable_gate_independent`).  H11 is `zipf_phase_transition`,
proved by feeding the `p`-series criterion into the main theorem.

Analyst: the forward direction is the informative one.  If the budget `K` works at every
context length then `τ · headMass w n ≤ headMass w K` for all `n`, i.e. the partial sums
are *bounded* — for a positive series, boundedness is summability.  The knee is thus a
finite-sample probe of an infinite-series property, which explains why a two-point
measurement can be genuinely predictive and also why it can never certify an exact value
(cf. `exact_flatness_refuted`).

Critic: the hypothesis `0 < τ` is load-bearing (with `τ ≤ 0` every profile is trivially
stable with `K = 0`) and so is `τ < 1` (at `τ = 1` no truncation below the context length
ever passes, and stability fails for every profile).  Both are interior conditions
satisfied by the measured gate `0.98`.
-/

open AttentionBudget

open Finset Filter

/-! ## The summability criterion -/




/-! ## The Zipf phase transition -/







open AttentionBudget in
theorem solution{w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (hsum : Summable w) {τ : ℝ}
    {k : ℕ} (hk : 1 ≤ k) (htail : ∑' i, w (i + k) ≤ (1 - τ) * w 0) {n : ℕ} (hn : 1 ≤ n) :
    kstar w n τ ≤ k := by
  have hshift : Summable (fun i => w (i + k)) := (summable_nat_add_iff k).mpr hsum
  have hT0 : 0 ≤ ∑' i, w (i + k) := tsum_nonneg fun i => (hw (i + k)).le
  have hw0 : 0 < w 0 := hw 0
  have hτ1 : τ ≤ 1 := by nlinarith
  apply kstar_le_of_pass
  rcases le_or_gt n k with h | h
  · rw [retained, min_eq_right h, div_self (headMass_pos hw hn).ne']
    exact hτ1
  · have hmin : min k n = k := min_eq_left h.le
    have hA : w 0 ≤ headMass w k := by
      have h1 : headMass w 1 ≤ headMass w k := headMass_mono hw hk
      simpa [headMass] using h1
    have hkpos : 0 < headMass w k := headMass_pos hw (by omega)
    have hdiff : headMass w n - headMass w k ≤ ∑' i, w (i + k) := by
      have hrange : headMass w n - headMass w k = ∑ j ∈ Finset.range (n - k), w (j + k) := by
        have h1 : headMass w n - headMass w k = ∑ i ∈ Finset.Ico k n, w i := by
          rw [Finset.sum_Ico_eq_sub _ h.le]
          simp [headMass]
        rw [h1, Finset.sum_Ico_eq_sum_range]
        exact Finset.sum_congr rfl fun j _ => by rw [add_comm]
      rw [hrange]
      exact hshift.sum_le_tsum _ fun i _ => (hw (i + k)).le
    rw [retained, hmin, le_div_iff₀ (headMass_pos hw hn)]
    have hnpos : 0 < headMass w n := headMass_pos hw hn
    rcases le_or_gt 0 τ with hτ0 | hτ0
    · nlinarith [mul_le_mul_of_nonneg_left hdiff hτ0,
        mul_nonneg (sub_nonneg.mpr hτ1) hT0,
        mul_nonneg (sub_nonneg.mpr hτ1) (sub_nonneg.mpr hA)]
    · nlinarith
