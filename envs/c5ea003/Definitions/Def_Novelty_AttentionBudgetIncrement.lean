-- Prove2me | Definitions.Def_Novelty_AttentionBudgetIncrement
-- name    : Novelty_AttentionBudgetIncrement
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:04:26.085245+00:00
-- url     : https://prove2.me/theorems/135ed20d-d5cf-4e27-b61a-6bc63d8d0e64
-- title:
--   Aether Catalog definitions — Novelty_AttentionBudgetIncrement
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AttentionBudgetIncrement`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AttentionBudgetIncrement.lean by skeleton subtraction
import Mathlib

/-!
# The attention-budget increment law (NET-67, discrete layer)

NET-67 measures, for two transformers of different parameter scale, the *knee*
of the top-`k` attention-retention curve: the smallest number `k` of retained
keys at which a drift-assert on the generated continuation still passes.
The measured grid (contexts `512, 1024, 2048`, i.e. `j = 0, 1, 2` doublings
above the base context) is

| model    | j = 0 | j = 1 | j = 2 |
|----------|-------|-------|-------|
| 0.5B     | 16    | 20    | 24    |
| 1.5B     | 16    | 16    | 18    |

and the verdict extracted from it is **SCALE-HALVES-THE-CONTEXT-INCREMENT**:
both curves start at `16`, the small model gains `+4` keys per context doubling,
the large model `+2`.

This file is the *discrete* layer of the formalisation.  It fixes the two
closed forms

* `kneeSmall j = 16 + 4 * j`  (exactly affine),
* `kneeLarge j = max 16 (14 + 2 * j)`  (a hinge: flat, then slope `2`),

proves that they reproduce the measured grid, and then audits the verdict.
Three of the results are *corrections* of the informal claim:

* `kneeLarge_not_affine` — the large-model curve is **not** of the form
  `k₀ + d * j` on the measured window at all: its increments are `0` then `+2`.
  So "slope 2" can only mean the *terminal* increment, never a global slope.
* `halving_is_terminal_not_average` — for the terminal increment the halving
  `4 ↦ 2` is correct, but the *average* increment over the measured window is
  `4 ↦ 1`: a quartering.  The two readings of the verdict genuinely disagree.
* `twenty_key_budget_does_not_cover_both` and `least_budget_at_2048` — the
  deployment corollary "a 20-key budget covers both models to 2048" is false;
  the least uniform budget at 2048 is `24`.

Finally the two laws are shown to *diverge* (`gap_unbounded`) with budget ratio
tending to `2` (`ratio_tendsto_two`): no fixed key budget survives unbounded
context, and asymptotically the small model needs exactly twice the keys.
-/

namespace Catalog.Novelty.AttentionBudgetIncrement

open Filter Topology

/-! ### 1. The two measured laws -/

/-- Attention-budget knee of the small (0.5B) model after `j` context doublings
above the base context `512`.  Measured: `16, 20, 24`. -/
def kneeSmall (j : ℕ) : ℕ := 16 + 4 * j

/-- Attention-budget knee of the large (1.5B) model after `j` context doublings.
Measured: `16, 16, 18` — a hinge, flat at the base level and then rising with
slope `2`. -/
def kneeLarge (j : ℕ) : ℕ := max 16 (14 + 2 * j)




/-! ### 2. Increments -/









/-! ### 3. Deployment: uniform key budgets -/

/-- A budget `B` is *safe at horizon* `j` if it covers the knee of both models
after `j` context doublings. -/
def SafeAt (B j : ℕ) : Prop := kneeSmall j ≤ B ∧ kneeLarge j ≤ B





/-! ### 4. Divergence of the two laws -/





end Catalog.Novelty.AttentionBudgetIncrement


