-- Prove2me | solution 1 for AttentionBudget.ctxStable_iff_summable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T19:58:31.049971+00:00
-- url     : https://prove2.me/submissions/89a92116-02fb-4e56-a960-acb8c85cd317
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Sol generated from Shared/AttentionBudgetSummability.lean
import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee
import Definitions.Def_Shared_AttentionBudgetScaling
import Definitions.Def_Shared_AttentionBudgetSummability
import Theorems.Thm_AttentionBudget_gate_le_retained_kstar
import Theorems.Thm_AttentionBudget_headMass_mono
import Theorems.Thm_AttentionBudget_headMass_pos
import Theorems.Thm_AttentionBudget_kstar_le_of_pass
import Theorems.Thm_AttentionBudget_retained_mono

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
theorem solution{w : ℕ → ℝ} (hw : ∀ i, 0 < w i) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ1 : τ < 1) : CtxStable w τ ↔ Summable w := by
  constructor
  · rintro ⟨K, hK⟩
    by_contra hns
    have htend : Tendsto (fun n => headMass w n) atTop atTop :=
      (not_summable_iff_tendsto_nat_atTop_of_nonneg fun i => (hw i).le).mp hns
    obtain ⟨n, hn1, hn2⟩ :=
      ((htend.eventually_gt_atTop (headMass w K / τ)).and (eventually_ge_atTop 1)).exists
    have hpass : τ ≤ retained w n K :=
      le_trans (gate_le_retained_kstar hw (by omega) hτ1.le)
        (retained_mono hw n (hK n hn2))
    have hnpos : 0 < headMass w n := headMass_pos hw (by omega)
    rw [retained, le_div_iff₀ hnpos] at hpass
    have hle : headMass w (min K n) ≤ headMass w K := headMass_mono hw (min_le_left _ _)
    rw [div_lt_iff₀ hτ0] at hn1
    linarith
  · intro hsum
    have hS : ∀ m, headMass w m ≤ ∑' i, w i := fun m =>
      hsum.sum_le_tsum _ (fun i _ => (hw i).le)
    have h1 : headMass w 1 = w 0 := by simp [headMass]
    have hSpos : 0 < ∑' i, w i := lt_of_lt_of_le (hw 0) (h1 ▸ hS 1)
    have htend : Tendsto (fun m => headMass w m) atTop (nhds (∑' i, w i)) :=
      hsum.hasSum.tendsto_sum_nat
    have hlt : τ * (∑' i, w i) < ∑' i, w i := by nlinarith
    obtain ⟨k, hk⟩ := (htend.eventually_const_lt hlt).exists
    refine ⟨k, fun n hn => kstar_le_of_pass ?_⟩
    rcases le_or_gt n k with h | h
    · have hmin : min k n = n := min_eq_right h
      rw [retained, hmin, div_self (headMass_pos hw hn).ne']
      linarith
    · have hmin : min k n = k := min_eq_left h.le
      rw [retained, hmin, le_div_iff₀ (headMass_pos hw hn)]
      have : τ * headMass w n ≤ τ * (∑' i, w i) :=
        mul_le_mul_of_nonneg_left (hS n) hτ0.le
      linarith
