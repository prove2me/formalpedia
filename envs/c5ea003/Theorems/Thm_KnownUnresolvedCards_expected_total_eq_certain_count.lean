-- Prove2me | Theorems.Thm_KnownUnresolvedCards_expected_total_eq_certain_count
-- name    : KnownUnresolvedCards.expected_total_eq_certain_count
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:41:10.969682+00:00
-- url     : https://prove2.me/theorems/a2f1ed3f-7296-4eb7-b28c-6e295818c8af
-- title:
--   Splitting theorem (headline form).
-- statement:
--   **Splitting theorem (headline form).**  `d` cards predicted with certainty
--   each pay one unit, the remaining cards are fair guesses; the expected payoff is
--   exactly `d = K.card`.  Uncertainty supplies no positive edge.
--
--   ```lean
--   theorem KnownUnresolvedCards.expected_total_eq_certain_count[Nonempty Ω]
--       (p : ι → Ω → ℚ) (K : Finset ι)
--       (hK : ∀ i ∈ K, Resolved (p i) 1)
--       (hU : ∀ i ∉ K, Fair (p i)) :
--       E (fun ω => ∑ i, p i ω) = (K.card : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/KnownUnresolvedCards/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/KnownUnresolvedCards/Basic.lean#L126

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











/-! ## Resolved and unresolved cards -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem KnownUnresolvedCards.expected_total_eq_certain_count[Nonempty Ω]
    (p : ι → Ω → ℚ) (K : Finset ι)
    (hK : ∀ i ∈ K, Resolved (p i) 1)
    (hU : ∀ i ∉ K, Fair (p i)) :
    E (fun ω => ∑ i, p i ω) = (K.card : ℚ) := by sorry
