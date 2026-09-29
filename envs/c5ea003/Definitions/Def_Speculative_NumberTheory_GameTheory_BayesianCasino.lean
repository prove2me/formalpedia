-- Prove2me | Definitions.Def_Speculative_NumberTheory_GameTheory_BayesianCasino
-- name    : Speculative_NumberTheory_GameTheory_BayesianCasino
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:33:43.764441+00:00
-- url     : https://prove2.me/theorems/a5047a0c-dc6b-4261-b20e-cb0d2a5cd53b
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_GameTheory_BayesianCasino
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.GameTheory.BayesianCasino`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/GameTheory/BayesianCasino.lean by skeleton subtraction
import Mathlib

/-!
# Gödel's Casino: sharp Bayesian and minimax laws

This file deepens the finite Boolean casino model.  A Bayesian card has a rational
probability `q` of being true.  We identify the optimal deterministic bet on every
card and prove the exact value of the whole deck: the sum of the absolute biases
`|2q-1|`.  Thus independence of a statement from a formal theory alone supplies
no edge; an edge is exactly probabilistic bias away from one half.

The second part allows a player to randomize among finitely many deterministic
strategies.  Complementing a world negates the mixed payoff, proving a finite
minimax/no-free-lunch theorem: every mixed strategy has a world with nonpositive
expected payoff.  No positivity or normalization assumption on the mixing weights
is needed for this obstruction.
-/

namespace GodelCasinoDeepening

/-- Unit payoff for predicting a Boolean truth value. -/
def unitPayoff (prediction truth : Bool) : ℤ :=
  if prediction = truth then 1 else -1

/-- Total unit-stake payoff on a finite deck. -/
def totalPayoff {n : ℕ} (strategy truth : Fin n → Bool) : ℤ :=
  ∑ i, unitPayoff (strategy i) (truth i)

/-- The world obtained by reversing every truth value. -/
def complementWorld {n : ℕ} (truth : Fin n → Bool) : Fin n → Bool :=
  fun i => !(truth i)

/-- Expected contribution of one card whose probability of truth is `q`. -/
def cardExpectedPayoff (q : ℚ) (prediction : Bool) : ℚ :=
  if prediction then 2 * q - 1 else 1 - 2 * q

/-- Expected payoff of a deterministic strategy from the cards' truth marginals. -/
def bayesianPayoff {n : ℕ} (q : Fin n → ℚ) (strategy : Fin n → Bool) : ℚ :=
  ∑ i, cardExpectedPayoff (q i) (strategy i)

/-- Bet true precisely when truth has probability at least one half. -/
def bayesStrategy {n : ℕ} (q : Fin n → ℚ) : Fin n → Bool :=
  fun i => decide ((1 : ℚ) / 2 ≤ q i)

/-
The Bayes bet realizes the absolute bias on each individual card.
-/

/-
No deterministic prediction beats the absolute bias available on one card.
-/

/-
**Exact Bayesian value theorem.**  Optimal expected deck profit is the sum of
absolute marginal biases.
-/

/-
The Bayes strategy dominates every deterministic strategy.
-/

/-
The casino has zero Bayesian value exactly when every card is fair.
-/

/-
A deck has a strictly positive optimal edge exactly when at least one card is
biased away from one half.
-/

/-
Exact one-card regret: disagreeing with the Bayes prediction costs twice the
available absolute bias, while agreeing costs nothing.
-/

/-
**Exact regret decomposition.**  The loss against the optimal strategy is the
sum of twice the biases precisely on the cards where the player's bet differs.
-/

/-
On a deck with no fair cards, the Bayes strategy is uniquely optimal.
-/

/-- Weighted payoff of a finite mixture of deterministic strategies in one world.
The weights may in particular be probabilities summing to one. -/
def mixedPayoff {m n : ℕ} (weight : Fin m → ℚ)
    (strategy : Fin m → Fin n → Bool) (truth : Fin n → Bool) : ℚ :=
  ∑ j, weight j * totalPayoff (strategy j) truth

/-
Complementing the world reverses the payoff of every mixed strategy.
-/

/-
**Mixed minimax/no-free-lunch theorem.**  For every finite randomized player,
there is a possible world where its expected payoff is nonpositive.
-/

/-
Consequently no finite mixed strategy can guarantee a strict win in every
possible truth assignment.
-/

end GodelCasinoDeepening


