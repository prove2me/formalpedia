-- Prove2me | Definitions.Def_Bridges_GameTheory_SpernerNashEquilibria
-- name    : Bridges_GameTheory_SpernerNashEquilibria
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:22:01.926402+00:00
-- url     : https://prove2.me/theorems/d6ef92cd-0498-4a2b-a03e-f13f620a91fa
-- title:
--   Aether Catalog definitions — Bridges_GameTheory_SpernerNashEquilibria
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GameTheory.SpernerNashEquilibria`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GameTheory/SpernerNashEquilibria.lean by skeleton subtraction
import Mathlib
/-
  Sperner's Lemma Implies Nash Equilibria:
  Combinatorial Fixed Points in Game Theory

  This module formalizes the connection between Sperner's lemma and Nash's theorem.
  The key insight: a Sperner coloring of the mixed strategy simplex derived from
  best-response correspondences yields approximate Nash equilibria whose limits
  are exact equilibria.
-/

open Finset BigOperators

noncomputable section

/-! ## Finite Normal-Form Games -/

/-- A finite normal-form game with `n` players, each having finitely many pure strategies. -/
structure FiniteGame where
  numPlayers : ℕ
  numPlayers_pos : 0 < numPlayers
  numStrats : Fin numPlayers → ℕ
  numStrats_pos : ∀ i, 0 < numStrats i
  payoff : (i : Fin numPlayers) → (∀ j : Fin numPlayers, Fin (numStrats j)) → ℝ

/-- A mixed strategy for player `i` is a probability distribution over pure strategies. -/
structure MixedStrategy (G : FiniteGame) (i : Fin G.numPlayers) where
  prob : Fin (G.numStrats i) → ℝ
  nonneg : ∀ s, 0 ≤ prob s
  sum_one : ∑ s : Fin (G.numStrats i), prob s = 1

/-- A mixed strategy profile assigns a mixed strategy to each player. -/
def MixedProfile (G : FiniteGame) := ∀ i : Fin G.numPlayers, MixedStrategy G i

/-- Expected payoff for player `i` under a mixed strategy profile. -/
noncomputable def expectedPayoff (G : FiniteGame) (σ : MixedProfile G)
    (i : Fin G.numPlayers) : ℝ :=
  ∑ s : (∀ j : Fin G.numPlayers, Fin (G.numStrats j)),
    (∏ j : Fin G.numPlayers, (σ j).prob (s j)) * G.payoff i s

/-- Expected payoff to player `i` when they deviate to pure strategy `si`. -/
noncomputable def deviationPayoff (G : FiniteGame) (σ : MixedProfile G)
    (i : Fin G.numPlayers) (si : Fin (G.numStrats i)) : ℝ :=
  ∑ s : (∀ j : Fin G.numPlayers, Fin (G.numStrats j)),
    (∏ j : Fin G.numPlayers,
      if h : j = i then
        if s j = h ▸ si then 1 else 0
      else (σ j).prob (s j)) * G.payoff i s

/-! ## Nash Equilibrium -/

/-- A mixed strategy profile is a Nash equilibrium if no player can improve
  their expected payoff by unilaterally deviating to any pure strategy. -/
def IsNashEquilibrium (G : FiniteGame) (σ : MixedProfile G) : Prop :=
  ∀ (i : Fin G.numPlayers) (si : Fin (G.numStrats i)),
    deviationPayoff G σ i si ≤ expectedPayoff G σ i

/-- A mixed strategy profile is an ε-approximate Nash equilibrium if no player
  can improve their expected payoff by more than ε by deviating. -/
def IsApproxNashEquilibrium (G : FiniteGame) (σ : MixedProfile G) (ε : ℝ) : Prop :=
  ∀ (i : Fin G.numPlayers) (si : Fin (G.numStrats i)),
    deviationPayoff G σ i si ≤ expectedPayoff G σ i + ε

/-
Every Nash equilibrium is an ε-approximate Nash equilibrium for any ε ≥ 0.
-/

/-! ## Combinatorial Fixed Points: A Novel Framework -/


/-
A profile is an ε-approximate Nash equilibrium iff every deviation gain is ≤ ε.
-/

/-
An exact Nash equilibrium is equivalent to a 0-approximate Nash equilibrium.
-/

/-! ## The Sperner Property -/


/-! ## The Bridge: Support Lemma and Sperner → Nash -/

/-
**The Support Lemma**: In a Nash equilibrium, every strategy played with
  positive probability achieves the maximum deviation payoff (equals the expected
  payoff). This is the fundamental structural property connecting combinatorial
  (Sperner) and analytic (Nash) fixed point theory.

  Proof insight: expectedPayoff = ∑ σ(si) * deviationPayoff(si) (convex combination),
  and Nash says deviationPayoff(si) ≤ expectedPayoff for all si. Since the weighted
  average of terms all ≤ expectedPayoff must equal expectedPayoff, any term with
  positive weight must equal expectedPayoff.
-/

/-! ## Regret and Convergence -/

/-- The regret of player `i` from strategy `si`. -/
noncomputable def regret (G : FiniteGame) (σ : MixedProfile G)
    (i : Fin G.numPlayers) (si : Fin (G.numStrats i)) : ℝ :=
  deviationPayoff G σ i si - expectedPayoff G σ i

/-
Approximate Nash iff all regrets are bounded.
-/

/-
Monotonicity: if ε₁ ≤ ε₂ and σ is an ε₁-Nash, then it's an ε₂-Nash.
-/

/-! ## Convexity of Mixed Strategy Payoffs -/

/-
Expected payoff equals the probability-weighted sum of deviation payoffs.
  This is the key multilinearity/convexity property of mixed strategies.
-/

/-
Every player has a pure strategy at least as good as their mixed strategy.
  This follows from the convexity property: a weighted average cannot exceed
  the maximum of its terms.
-/

/-
Every player has a pure strategy at most as good as their mixed strategy.
-/

/-! ## Combinatorial Equilibrium Refinement -/



/-! ## Payoff Bounds -/

/-
Expected payoff is bounded by M when all payoffs are bounded by M.
-/

/-
Deviation payoff is bounded by M when all payoffs are bounded by M.
-/

/-
Regret is bounded by 2M when payoffs are bounded by M.
-/

end


