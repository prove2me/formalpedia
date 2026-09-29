-- Prove2me | Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
-- name    : MachineLearning_KnownUnresolvedCards_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:45:28.392518+00:00
-- url     : https://prove2.me/theorems/fc0aaa34-ae0a-42b1-89d4-424d66764472
-- title:
--   Aether Catalog definitions — MachineLearning_KnownUnresolvedCards_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.KnownUnresolvedCards.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/KnownUnresolvedCards/Basic.lean by skeleton subtraction
import Mathlib
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


namespace KnownUnresolvedCards

open Finset

/-! ## Uniform expectation on a finite sample space -/

variable {Ω : Type*} [Fintype Ω]

/-- The expectation of a rational observable `f` under the uniform law on the
finite sample space `Ω`. -/
def E (f : Ω → ℚ) : ℚ := (∑ ω, f ω) / (Fintype.card Ω : ℚ)








/-- The variance of a rational observable under the uniform law. -/
def Var (f : Ω → ℚ) : ℚ := E (fun ω => f ω ^ 2) - (E f) ^ 2


/-! ## Resolved and unresolved cards -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A card is *resolved with value `c`* when its payoff is the constant `c`:
the predictor knows the card and collects `c` in every state of the world. -/
def Resolved (p : Ω → ℚ) (c : ℚ) : Prop := ∀ ω, p ω = c

/-- A card is *fair* when its payoff has zero mean: the odds offered exactly
compensate the residual uncertainty. -/
def Fair (p : Ω → ℚ) : Prop := E p = 0





end KnownUnresolvedCards


