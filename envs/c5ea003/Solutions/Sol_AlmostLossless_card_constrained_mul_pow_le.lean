-- Prove2me | solution 1 for AlmostLossless.card_constrained_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:05:23.716066+00:00
-- url     : https://prove2.me/submissions/8d9fb7ed-99ab-4185-8a56-a52403c164f5

-- Sol generated from Bridges/AlmostLosslessTwiseIndependent.lean
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






open AlmostLossless in
theorem solution{T : ℕ} (x : α) (s : Finset α)
    (hs : s.card = T) (hx : x ∉ s) :
    (Finset.univ.filter (fun f : α → Fin M => ∀ y ∈ s, f y = f x)).card * M ^ T
      ≤ Fintype.card (α → Fin M) := by
  classical
  set A : Finset (α → Fin M) :=
    Finset.univ.filter (fun f : α → Fin M => ∀ y ∈ s, f y = f x) with hA
  set B : Finset (↥s → Fin M) := Finset.univ with hB
  have hcards : Fintype.card (↥s → Fin M) = M ^ T := by
    rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, hs]
  have hprod : (A ×ˢ B).card = A.card * M ^ T := by
    rw [Finset.card_product, hB, Finset.card_univ, hcards]
  set glue : ((α → Fin M) × (↥s → Fin M)) → (α → Fin M) :=
    fun p z => if h : z ∈ s then p.2 ⟨z, h⟩ else p.1 z with hglue
  have hinj : Set.InjOn glue ↑(A ×ˢ B) := by
    intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_product, hA, Finset.mem_filter,
      Finset.mem_univ, true_and] at hp hq
    have hval : ∀ z : α, (if h : z ∈ s then p.2 ⟨z, h⟩ else p.1 z)
        = (if h : z ∈ s then q.2 ⟨z, h⟩ else q.1 z) := fun z => congrFun hpq z
    have hxeq : p.1 x = q.1 x := by
      have := hval x
      simpa [hx] using this
    have hfst : p.1 = q.1 := by
      funext z
      by_cases hz : z ∈ s
      · rw [hp.1 z hz, hq.1 z hz, hxeq]
      · have := hval z
        simpa [hz] using this
    have hsnd : p.2 = q.2 := by
      funext z
      have := hval z.1
      simpa [z.2] using this
    exact Prod.ext hfst hsnd
  have hmaps : ∀ p ∈ A ×ˢ B, glue p ∈ (Finset.univ : Finset (α → Fin M)) :=
    fun p _ => Finset.mem_univ _
  have hle := Finset.card_le_card_of_injOn glue hmaps hinj
  rw [hprod, Finset.card_univ] at hle
  exact hle
