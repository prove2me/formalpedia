-- Prove2me | Theorems.Thm_AlmostLossless_exists_list_scheme_exponential
-- name    : AlmostLossless.exists_list_scheme_exponential
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:08:17.179856+00:00
-- url     : https://prove2.me/theorems/b1672515-d9b7-4130-b2af-99bda9c36def
-- title:
--   The exponential gain, in readable form.
-- statement:
--   **The exponential gain, in readable form.**  Since `C(n,T) ≤ n^T`, the
--   failure probability of the list-`T` scheme is at most `δ + (|l|/M)^T`: for a
--   codebook of size `|l| ≤ M/2` the collision term is at most `2^{-T}`, versus
--   `|l|/(T·M) ≥ 1/(2T)` from 2-universality alone.
--
--   ```lean
--   theorem AlmostLossless.exists_list_scheme_exponential(μ : FinProbDist α) {H : Fin K → α → Fin M}
--       {T : ℕ} (hI : IndepT H T) (hK : 0 < K) (hM : 0 < M)
--       (l : List α) (hnd : l.Nodup) (δ : ℝ) (hδ : setMass μ (l.toFinset)ᶜ ≤ δ) :
--       ∃ k : Fin K,
--         setMass μ (Finset.univ.filter
--             (fun x => ¬ (listHashScheme T l (H k)).Succeeds x))
--             ≤ δ + ((l.length : ℝ) / M) ^ T
--         ∧ (∀ i : Fin M, ((listHashScheme T l (H k)).dec i).length ≤ T) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessTwiseIndependent.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessTwiseIndependent.lean#L285

-- Thm stub generated from Bridges/AlmostLosslessTwiseIndependent.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessTwiseIndependent
import Definitions.Def_Bridges_MinEntropy
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

theorem AlmostLossless.exists_list_scheme_exponential(μ : FinProbDist α) {H : Fin K → α → Fin M}
    {T : ℕ} (hI : IndepT H T) (hK : 0 < K) (hM : 0 < M)
    (l : List α) (hnd : l.Nodup) (δ : ℝ) (hδ : setMass μ (l.toFinset)ᶜ ≤ δ) :
    ∃ k : Fin K,
      setMass μ (Finset.univ.filter
          (fun x => ¬ (listHashScheme T l (H k)).Succeeds x))
          ≤ δ + ((l.length : ℝ) / M) ^ T
      ∧ (∀ i : Fin M, ((listHashScheme T l (H k)).dec i).length ≤ T) := by sorry
