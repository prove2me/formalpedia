-- Prove2me | solution 1 for TropicalShtarkov.shtarkovSum_le_card_image
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:56:40.80298+00:00
-- url     : https://prove2.me/submissions/e484e686-0b9c-4b4b-af8d-fca2958a58d1

-- Sol generated from Tropical/Shtarkov/Basic.lean
import Mathlib
import Definitions.Def_Tropical_Shtarkov_Basic
/-
# Tropical Shtarkov Sums: the abstract layer

## Bridge: max-plus (tropical) algebra ↔ universal source coding ↔ counting

The *Shtarkov sum* (a.k.a. the normalizing constant of the normalized maximum
likelihood distribution) of a model class `{P i}` on a finite sample space `X` is

  `S(P) = ∑_{x ∈ X} sup_i P i x`.

The inner `sup` is exactly a **tropical (max-plus) sum** of the log-likelihoods:
`log sup_i P i x = ⊕_i log P i x`, so `S(P)` is the classical mass of the
tropicalisation of the class, and `log S(P)` is the minimax pointwise regret of
the class.  This file develops the two structural tools used throughout:

* `shtarkovSum_ge_packing` — a *packing* lower bound: any collection of
  (sample, model) pairs contributes to `S`;
* `shtarkovSum_le_card_image` — a *sufficient statistic* upper bound: if the
  pointwise supremum is dominated by a sub-probability measure depending on `x`
  only through a statistic `T`, then `S ≤ |image T|`.

Together with the one-dimensional maximum-likelihood inequality
`bernoulli_ml_le` these give matching upper/lower bounds for finite-state
classes in `Catalog/Tropical/Shtarkov/FiniteState.lean`.
-/


open Finset

open TropicalShtarkov

/-! ## The Shtarkov sum -/

variable {X ι : Type*} [Fintype X]







/-! ## The one-dimensional maximum-likelihood inequality

For a Bernoulli source observed `a` times as `true` and `b` times as `false`,
the likelihood `θ^a (1-θ)^b` is maximised at the empirical frequency
`a / (a+b)`.  This is the analytic core of the finite-state upper bound; the
proof is the Gibbs/`log x ≤ x - 1` argument. -/







open TropicalShtarkov in
theorem solution{Y : Type*} [DecidableEq Y] [Nonempty ι]
    (P : ι → X → ℝ) (T : X → Y) (q : Y → X → ℝ)
    (hdom : ∀ i x, P i x ≤ q (T x) x)
    (hqnn : ∀ y x, 0 ≤ q y x)
    (hqsum : ∀ y, ∑ x : X, q y x ≤ 1) :
    shtarkovSum P ≤ (((univ : Finset X).image T).card : ℝ) := by
  have step1 : shtarkovSum P ≤ ∑ x : X, q (T x) x :=
    Finset.sum_le_sum fun x _ => ciSup_le fun i => hdom i x
  have step2 : ∑ x : X, q (T x) x
      = ∑ y ∈ univ.image T, ∑ x ∈ univ with T x = y, q (T x) x :=
    (Finset.sum_fiberwise_of_maps_to (fun x _ => mem_image_of_mem T (mem_univ x)) _).symm
  have step3 : ∀ y ∈ univ.image T, (∑ x ∈ univ with T x = y, q (T x) x) ≤ 1 := by
    intro y _
    have : (∑ x ∈ univ with T x = y, q (T x) x) = ∑ x ∈ univ with T x = y, q y x := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(mem_filter.mp hx).2]
    rw [this]
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun x _ _ => hqnn y x) (hqsum y)
  calc shtarkovSum P ≤ ∑ x : X, q (T x) x := step1
    _ = ∑ y ∈ univ.image T, ∑ x ∈ univ with T x = y, q (T x) x := step2
    _ ≤ ∑ _y ∈ univ.image T, (1 : ℝ) := Finset.sum_le_sum step3
    _ = (((univ : Finset X).image T).card : ℝ) := by simp
