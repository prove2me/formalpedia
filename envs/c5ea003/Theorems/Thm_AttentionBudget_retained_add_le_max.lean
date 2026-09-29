-- Prove2me | Theorems.Thm_AttentionBudget_retained_add_le_max
-- name    : AttentionBudget.retained_add_le_max
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:18:07.032899+00:00
-- url     : https://prove2.me/theorems/fa34d920-c478-4e7c-b576-5374012a4480
-- title:
--   The upper half of the mediant inequality: mixing two heads is never better than the
-- statement:
--   The upper half of the mediant inequality: mixing two heads is never better than the
--   better head.
--
--   ```lean
--   theorem AttentionBudget.retained_add_le_max(hw₁ : ∀ i, 0 < w₁ i) (hw₂ : ∀ i, 0 < w₂ i) (hn : 0 < n)
--       (k : ℕ) :
--       retained (fun i => w₁ i + w₂ i) n k ≤ max (retained w₁ n k) (retained w₂ n k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/AttentionBudgetScaling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/AttentionBudgetScaling.lean#L183

-- Thm stub generated from Shared/AttentionBudgetScaling.lean
import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee
import Definitions.Def_Shared_AttentionBudgetScaling

/-!
# Scaling laws for the attention budget: closed form, head merging, and the limits of
"flatness"

This is the second research cycle built on `Shared.AttentionBudgetKnee`.  Three
questions left open there are settled here.

1. **Closed form for the universal budget.**  `kstar_le_geometricBudget` replaces the
   existence statement of cycle 1 by the explicit value
   `K(r, τ) = max ⌈log((1-τ)(1-r)) / log r⌉ 1`, valid at *every* context length.
   Solving the formula for `r` turns a measured knee into a bound on the decay ratio of
   the attention profile, a model-internal quantity: the knee is a *spectrometer*.

2. **Is the flat chain literally flat?**  No.  `exact_flatness_refuted` computes the
   knee of the ideal geometric profile `(1/2)^i` at two context lengths and finds
   `k*(1) = 1 ≠ 2 = k*(2)`.  The normaliser grows with the context, so the retained
   fraction is *antitone* in `n` (`retained_antitone_context`).  Hence an observed
   `{16, 16}` cannot be upgraded to an equality law; the correct invariant is uniform
   boundedness, characterised by `ctxStable_iff_uniform_pass`.

3. **What happens when heads are merged?**  Context stability is closed under mixing
   (`ctxStable_add`): the knee of a two-head mixture is sandwiched between the two
   per-head knees (`min_le_kstar_add`, `kstar_add_le_max`), because retained mass is a
   *mediant* of the per-head retained masses (`retained_add_ge_min`,
   `retained_add_le_max`).  A context-stable model therefore cannot be destabilised by
   adding further context-stable heads — while by `kstar_ge_of_bounded_ratio` a single
   gapless head already destroys stability (`not_ctxStable_uniform`).  Stability is a
   property of the *worst* head: a max law, not a sum law.

-- !-- Lab Notes -- !--
Hypothesizer (cycle 2):
 (H6) The budget admits a closed form in `(r, τ)` alone — no dependence on context
      length or on the head count.                                          [BOLD]
 (H7) Exact flatness `k*(2n) = k*(n)` is false even for the ideal geometric
      profile; only boundedness survives.
 (H8) Context stability is closed under head mixing and is decided by the worst
      head (a max law, not a sum law).                                      [BOLD]

Experimenter: H6 = `kstar_le_geometricBudget`; H7 = `exact_flatness_refuted`
(explicit computation: retained mass `2/3 < 3/4` at `k = 1`, `n = 2`, while the same
gate is cleared at `n = 1` by `k = 1`); H8 = `ctxStable_add` via the mediant
inequality.  All proved, zero sorries.

Analyst: the mediant inequality is the structural reason a *max* law appears rather
than a sum law: `(A₁+A₂)/(B₁+B₂)` is squeezed between `A₁/B₁` and `A₂/B₂`, so mixing is
never worse than the worst head.  This predicts that per-head knees measured separately
should bracket the model-level knee — a directly testable consequence.

Critic: `exact_flatness_refuted` is a genuine falsification, not a corner case: the
profile is the canonical geometric one and the gate `3/4` is interior.  Its moral is
that any claimed "flat chain" must be reported as a bracket, exactly as `knee_bracket`
demands.
-/

open AttentionBudget

open Finset

/-! ## Context stability -/



/-! ## A closed form for the universal budget -/




/-! ## Retained mass decays with context length -/


/-! ## H7: exact flatness is false -/


/-! ## H8: merging heads — the mediant law -/


variable {w₁ w₂ : ℕ → ℝ} {τ : ℝ} {n : ℕ}

theorem AttentionBudget.retained_add_le_max(hw₁ : ∀ i, 0 < w₁ i) (hw₂ : ∀ i, 0 < w₂ i) (hn : 0 < n)
    (k : ℕ) :
    retained (fun i => w₁ i + w₂ i) n k ≤ max (retained w₁ n k) (retained w₂ n k) := by sorry
