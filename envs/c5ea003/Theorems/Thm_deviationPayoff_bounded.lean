-- Prove2me | Theorems.Thm_deviationPayoff_bounded
-- name    : deviationPayoff_bounded
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:30:43.819601+00:00
-- url     : https://prove2.me/theorems/f58b3729-77b2-429f-a2a8-d3f0afca97e4
-- title:
--   DeviationPayoff bounded
-- statement:
--   Formal statement of `deviationPayoff_bounded` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem deviationPayoff_bounded(G : FiniteGame) (σ : MixedProfile G)
--       (i : Fin G.numPlayers) (si : Fin (G.numStrats i)) (M : ℝ) (_hM : 0 ≤ M)
--       (hbound : ∀ j s, |G.payoff j s| ≤ M) :
--       |deviationPayoff G σ i si| ≤ M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GameTheory/SpernerNashEquilibria.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GameTheory/SpernerNashEquilibria.lean#L258

-- Thm stub generated from Bridges/GameTheory/SpernerNashEquilibria.lean
import Mathlib
import Definitions.Def_Bridges_GameTheory_SpernerNashEquilibria
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






/-! ## Nash Equilibrium -/



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
set_option maxHeartbeats 400000 in

theorem deviationPayoff_bounded(G : FiniteGame) (σ : MixedProfile G)
    (i : Fin G.numPlayers) (si : Fin (G.numStrats i)) (M : ℝ) (_hM : 0 ≤ M)
    (hbound : ∀ j s, |G.payoff j s| ≤ M) :
    |deviationPayoff G σ i si| ≤ M := by sorry
