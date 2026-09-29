-- Prove2me | solution 1 for AlmostLossless.fullFamily_indepT
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:19:28.151983+00:00
-- url     : https://prove2.me/submissions/33d6868d-9f70-4d2b-bbd7-0aca47f60749

-- Sol generated from Bridges/AlmostLosslessTwiseIndependent.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessTwiseIndependent
import Theorems.Thm_AlmostLossless_card_constrained_mul_pow_le
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






open AlmostLossless in
theorem solution(T : ℕ) : IndepT (fullFamily α M) T := by
  classical
  intro x s hs hx
  set e := Fintype.equivFin (α → Fin M) with he
  have hbij : (Finset.univ.filter
        (fun k => ∀ y ∈ s, fullFamily α M k y = fullFamily α M k x)).card
      = (Finset.univ.filter (fun f : α → Fin M => ∀ y ∈ s, f y = f x)).card := by
    refine Finset.card_bij (fun k _ => e.symm k) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      simpa [fullFamily, he] using hk
    · intro k₁ _ k₂ _ h
      exact e.symm.injective h
    · intro f hf
      refine ⟨e f, ?_, by simp [he]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      simpa [fullFamily, he] using hf
  rw [hbij]
  have hcount := card_constrained_mul_pow_le (M := M) x s hs hx
  have hcast : (((Finset.univ.filter (fun f : α → Fin M => ∀ y ∈ s, f y = f x)).card
      * M ^ T : ℕ) : ℝ) ≤ ((Fintype.card (α → Fin M) : ℕ) : ℝ) := by
    exact_mod_cast hcount
  push_cast at hcast
  exact hcast
