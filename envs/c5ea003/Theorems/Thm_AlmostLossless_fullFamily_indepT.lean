-- Prove2me | Theorems.Thm_AlmostLossless_fullFamily_indepT
-- name    : AlmostLossless.fullFamily_indepT
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:08:37.59082+00:00
-- url     : https://prove2.me/theorems/d139a5bf-e68a-4c12-97cc-2a65da63c9c5
-- title:
--   Non-vacuity.
-- statement:
--   **Non-vacuity.**  The full function family satisfies `IndepT` for *every*
--   `T`, so the hypotheses used above are satisfiable at all levels of independence
--   (at the price of a large key).
--
--   ```lean
--   theorem AlmostLossless.fullFamily_indepT(T : ℕ) : IndepT (fullFamily α M) T := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessTwiseIndependent.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessTwiseIndependent.lean#L368

-- Thm stub generated from Bridges/AlmostLosslessTwiseIndependent.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessTwiseIndependent
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression X: `T`-wise Independence and Factorial Moments

## Bridge: higher independence (algebra) ↔ factorial moments (combinatorics)
##         ↔ list decoding (coding theory)

`AlmostLosslessListDecoding` bounds the failure probability of list-`T` decoding
by `δ + |S|/(T·M)`: the gain from a longer list is only **linear** in `T`,
because a first-moment (Markov) estimate on the number of collisions is all that
2-universality provides.

This file proves that higher independence turns that linear gain into an
**exponential** one, settling Conjecture 3 / sub-conjecture C3a of the previous
cycle.  The right statistic is the `T`-th *factorial* moment: instead of counting
collisions, count `T`-element sets of colliding partners.

* `IndepT` — the counting form of `(T+1)`-wise independence: for any `T` symbols
  and a distinct symbol `x`, at most a `M^{-T}` fraction of the keys make all of
  them collide with `x`;
* `universal2_of_indepT` — coherence: `IndepT H 1` is exactly 2-universality;
* `sum_choose_collisionSet_le` — **the factorial-moment identity**
  `(∑ₖ C(collisions(k), T))·M^T ≤ K·C(|S|,T)`, proved by double counting over
  `T`-subsets;
* `card_badKeysT_indep_le` — hence at most a `C(|S|,T)/M^T` fraction of keys are
  bad, versus `|S|/(T·M)` from the first moment;
* `exists_list_scheme_indepT` — **the deliverable**: list-`T` decoding with
  failure probability `≤ δ + C(|l|,T)/M^T`, list length `≤ T` and cost exactly
  `|l|`;
* `exists_list_scheme_exponential` — the readable form `δ + (|l|/M)^T`:
  exponentially small in the list size.

## Impact: factorial_moment_bound, exponential_list_decoding_gain
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless


variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}










/-! ## Non-vacuity: the full function family is `T`-wise independent -/


variable {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ}

theorem AlmostLossless.fullFamily_indepT(T : ℕ) : IndepT (fullFamily α M) T := by sorry
