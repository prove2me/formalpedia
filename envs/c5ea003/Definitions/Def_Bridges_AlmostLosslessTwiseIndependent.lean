-- Prove2me | Definitions.Def_Bridges_AlmostLosslessTwiseIndependent
-- name    : Bridges_AlmostLosslessTwiseIndependent
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:11:45.271485+00:00
-- url     : https://prove2.me/theorems/df56e35a-8db6-46e9-90a9-ac8ce462ad5e
-- title:
--   Aether Catalog definitions — Bridges_AlmostLosslessTwiseIndependent
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlmostLosslessTwiseIndependent`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlmostLosslessTwiseIndependent.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessListDecoding
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

namespace AlmostLossless

section Independence

variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}

/-- **`(T+1)`-wise independence, counting form.**  For every set `s` of `T`
symbols and every symbol `x ∉ s`, at most a `M^{-T}` fraction of the keys send
all of `s` to the same value as `x`.  For `T = 1` this is exactly
2-universality (`universal2_of_indepT`). -/
def IndepT (H : Fin K → α → Fin M) (T : ℕ) : Prop :=
  ∀ (x : α) (s : Finset α), s.card = T → x ∉ s →
    ((Finset.univ.filter (fun k => ∀ y ∈ s, H k y = H k x)).card : ℝ) * (M : ℝ) ^ T
      ≤ K








end Independence

/-! ## Non-vacuity: the full function family is `T`-wise independent -/

section FullFamily

variable {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ}


/-- The family of **all** functions `α → Fin M`, indexed by `Fin K` with
`K = M^{|α|}`: the extreme case of a random codebook, with full independence. -/
noncomputable def fullFamily (α : Type*) [Fintype α] [DecidableEq α] (M : ℕ) :
    Fin (Fintype.card (α → Fin M)) → α → Fin M :=
  fun k => (Fintype.equivFin (α → Fin M)).symm k


end FullFamily

end AlmostLossless


