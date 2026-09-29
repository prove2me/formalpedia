-- Prove2me | solution 1 for KnownUnresolvedCards.E_const
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:31:30.529982+00:00
-- url     : https://prove2.me/submissions/1e1f49c5-48d8-4ba1-bbfc-5d625b4acc80

-- Sol generated from MachineLearning/KnownUnresolvedCards/Basic.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Theorems.Thm_KnownUnresolvedCards_E_def
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



lemma card_ne_zero [Nonempty Ω] : ((Fintype.card Ω : ℚ)) ≠ 0 := by
  have : 0 < Fintype.card Ω := Fintype.card_pos
  positivity








/-! ## Resolved and unresolved cards -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]








open KnownUnresolvedCards in
@[simp] theorem solution[Nonempty Ω] (c : ℚ) : E (fun _ : Ω => c) = c := by
  have h := card_ne_zero (Ω := Ω)
  rw [E_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
