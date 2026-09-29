-- Prove2me | Theorems.Thm_exists_pure_at_most_as_good
-- name    : exists_pure_at_most_as_good
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:31:24.112186+00:00
-- url     : https://prove2.me/theorems/26773ffc-2b6b-4a46-8605-76ad7a4c69db
-- title:
--   Exists pure at most as good
-- statement:
--   Formal statement of `exists_pure_at_most_as_good` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem exists_pure_at_most_as_good(G : FiniteGame) (σ : MixedProfile G)
--       (i : Fin G.numPlayers) :
--       ∃ si : Fin (G.numStrats i),
--         deviationPayoff G σ i si ≤ expectedPayoff G σ i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GameTheory/SpernerNashEquilibria.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GameTheory/SpernerNashEquilibria.lean#L203

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

theorem exists_pure_at_most_as_good(G : FiniteGame) (σ : MixedProfile G)
    (i : Fin G.numPlayers) :
    ∃ si : Fin (G.numStrats i),
      deviationPayoff G σ i si ≤ expectedPayoff G σ i := by sorry
