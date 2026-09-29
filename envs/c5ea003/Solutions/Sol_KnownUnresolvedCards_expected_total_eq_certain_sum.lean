-- Prove2me | solution 1 for KnownUnresolvedCards.expected_total_eq_certain_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:41:26.193618+00:00
-- url     : https://prove2.me/submissions/c1280d39-9d23-4a02-92cc-795e2cb46c77

-- Sol generated from MachineLearning/KnownUnresolvedCards/Basic.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Theorems.Thm_KnownUnresolvedCards_E_const
import Theorems.Thm_KnownUnresolvedCards_E_sum
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Known versus unresolved cards — I. The uniform expectation calculus

A *prediction game* pays a rational amount on each of finitely many **cards**.
Some cards are **resolved**: the predictor knows their value and collects a
deterministic unit payoff.  The remaining cards are **unresolved**: the predictor
must guess, and the guess is priced at *fair odds*, i.e. the payoff on such a
card has zero mean.

This file develops the minimal probabilistic infrastructure needed to state and
prove the headline principle

> `E[total payoff] = (number of resolved cards)`,

namely a uniform-expectation functional `E` on a finite sample space, its
linearity, and the **splitting theorem** `expected_total_eq_certain_count`.

The point of stating the splitting theorem for an *arbitrary* finite index type
`ι` and an *arbitrary* subset `K : Finset ι` of resolved cards is that the deck
models of `PermCount.lean` and `DeckGame.lean` are then genuine instances rather
than re-proofs.

## Main results

* `E_sum` — linearity of uniform expectation over a `Finset` sum.
* `expected_total_eq_certain_count` — if every card of `K` pays a deterministic
  `1` and every card outside `K` is fair, the expected total payoff is `K.card`.
* `expected_total_eq_certain_sum` — the weighted version with arbitrary
  deterministic payoffs on `K`.
* `no_fair_portfolio_edge` — a portfolio consisting only of fair cards has zero
  expected payoff, *whatever* the (possibly wildly correlated) joint law.
-/


open KnownUnresolvedCards

open Finset

/-! ## Uniform expectation on a finite sample space -/

variable {Ω : Type*} [Fintype Ω]











/-! ## Resolved and unresolved cards -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



lemma E_of_resolved [Nonempty Ω] {p : Ω → ℚ} {c : ℚ} (h : Resolved p c) : E p = c := by
  have hp : (fun ω : Ω => p ω) = (fun _ : Ω => c) := funext h
  simp [show p = (fun _ : Ω => c) from hp]





open KnownUnresolvedCards in
theorem solution[Nonempty Ω]
    (p : ι → Ω → ℚ) (K : Finset ι) (c : ι → ℚ)
    (hK : ∀ i ∈ K, Resolved (p i) (c i))
    (hU : ∀ i ∉ K, Fair (p i)) :
    E (fun ω => ∑ i, p i ω) = ∑ i ∈ K, c i := by
  classical
  rw [E_sum]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ K)]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i => i ∈ K), E (p i) = ∑ i ∈ K, c i := by
    have : Finset.univ.filter (fun i => i ∈ K) = K := by
      ext i; simp
    rw [this]
    exact Finset.sum_congr rfl fun i hi => E_of_resolved (hK i hi)
  have h2 : ∑ i ∈ Finset.univ.filter (fun i => i ∉ K), E (p i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hU i (by simpa using (Finset.mem_filter.mp hi).2)
  rw [h1, h2, add_zero]
