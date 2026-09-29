-- Prove2me | Theorems.Thm_AttentionBudget_ctxStable_iff_summable
-- name    : AttentionBudget.ctxStable_iff_summable
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:17:37.890476+00:00
-- url     : https://prove2.me/theorems/6a6bce8b-e8af-4806-9b56-21cfddd1988a
-- title:
--   H9/H10 â the summability criterion.
-- statement:
--   **H9/H10 â the summability criterion.**  A positive attention profile admits a
--   context-independent key budget at some (equivalently, every) interior gate exactly when
--   the profile is summable.
--
--   ```lean
--   theorem AttentionBudget.ctxStable_iff_summable{w : ℕ → ℝ} (hw : ∀ i, 0 < w i) {τ : ℝ} (hτ0 : 0 < τ)
--       (hτ1 : τ < 1) : CtxStable w τ ↔ Summable w := by sorry
--
--
--   /-! ## The Zipf phase transition -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/AttentionBudgetSummability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/AttentionBudgetSummability.lean#L59

-- Thm stub generated from Shared/AttentionBudgetSummability.lean
import Mathlib
import Definitions.Def_Shared_AttentionBudgetScaling
import Definitions.Def_Shared_AttentionBudgetSummability

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

theorem AttentionBudget.ctxStable_iff_summable{w : ℕ → ℝ} (hw : ∀ i, 0 < w i) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ1 : τ < 1) : CtxStable w τ ↔ Summable w := by sorry
