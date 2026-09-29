-- Prove2me | Theorems.Thm_AlmostLossless_card_constrained_mul_pow_le
-- name    : AlmostLossless.card_constrained_mul_pow_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:06:53.69586+00:00
-- url     : https://prove2.me/theorems/894922b7-d66e-4764-8fb1-5fbda24e94b2
-- title:
--   Counting the functions constrained to agree with `f x` on a set `s` of size
-- statement:
--   Counting the functions constrained to agree with `f x` on a set `s` of size
--   `T` avoiding `x`: they form at most a `M^{-T}` fraction of all functions.  The
--   proof glues a constrained function to an arbitrary pattern on `s`, which is an
--   injection into the full function space.
--
--   ```lean
--   theorem AlmostLossless.card_constrained_mul_pow_le{T : ℕ} (x : α) (s : Finset α)
--       (hs : s.card = T) (hx : x ∉ s) :
--       (Finset.univ.filter (fun f : α → Fin M => ∀ y ∈ s, f y = f x)).card * M ^ T
--         ≤ Fintype.card (α → Fin M) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessTwiseIndependent.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessTwiseIndependent.lean#L318

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

theorem AlmostLossless.card_constrained_mul_pow_le{T : ℕ} (x : α) (s : Finset α)
    (hs : s.card = T) (hx : x ∉ s) :
    (Finset.univ.filter (fun f : α → Fin M => ∀ y ∈ s, f y = f x)).card * M ^ T
      ≤ Fintype.card (α → Fin M) := by sorry
