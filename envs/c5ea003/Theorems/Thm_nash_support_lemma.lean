-- Prove2me | Theorems.Thm_nash_support_lemma
-- name    : nash_support_lemma
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:34:19.978847+00:00
-- url     : https://prove2.me/theorems/ae094677-9521-4671-8794-c990d1608ded
-- title:
--   Nash support lemma
-- statement:
--   Formal statement of `nash_support_lemma` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem nash_support_lemma(G : FiniteGame) (σ : MixedProfile G)
--       (hNash : IsNashEquilibrium G σ)
--       (i : Fin G.numPlayers) (si : Fin (G.numStrats i))
--       (hpos : 0 < (σ i).prob si) :
--       deviationPayoff G σ i si = expectedPayoff G σ i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GameTheory/SpernerNashEquilibria.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GameTheory/SpernerNashEquilibria.lean#L121

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

theorem nash_support_lemma(G : FiniteGame) (σ : MixedProfile G)
    (hNash : IsNashEquilibrium G σ)
    (i : Fin G.numPlayers) (si : Fin (G.numStrats i))
    (hpos : 0 < (σ i).prob si) :
    deviationPayoff G σ i si = expectedPayoff G σ i := by sorry
