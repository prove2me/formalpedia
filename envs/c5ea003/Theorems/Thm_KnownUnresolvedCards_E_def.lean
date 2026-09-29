-- Prove2me | Theorems.Thm_KnownUnresolvedCards_E_def
-- name    : KnownUnresolvedCards.E_def
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:38:59.600662+00:00
-- url     : https://prove2.me/theorems/ecbc93c4-4f6e-4386-86c5-85162c1caef9
-- title:
--   E def
-- statement:
--   Formal statement of `KnownUnresolvedCards.E_def` from the Aether Catalog (MachineLearning). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem KnownUnresolvedCards.E_def(f : Ω → ℚ) : E f = (∑ ω, f ω) / (Fintype.card Ω : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/KnownUnresolvedCards/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/KnownUnresolvedCards/Basic.lean#L50

-- Thm stub generated from MachineLearning/KnownUnresolvedCards/Basic.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
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

theorem KnownUnresolvedCards.E_def(f : Ω → ℚ) : E f = (∑ ω, f ω) / (Fintype.card Ω : ℚ) := by sorry
