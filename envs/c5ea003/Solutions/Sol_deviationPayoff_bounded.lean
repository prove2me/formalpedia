-- Prove2me | solution 1 for deviationPayoff_bounded
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:07:05.511614+00:00
-- url     : https://prove2.me/submissions/1ce9bfdd-2ba0-4a6d-9fa8-5085e6b522ff

-- Sol generated from Bridges/GameTheory/SpernerNashEquilibria.lean
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

/-
Regret is bounded by 2M when payoffs are bounded by M.
-/


set_option maxHeartbeats 400000 in
theorem solution(G : FiniteGame) (σ : MixedProfile G)
    (i : Fin G.numPlayers) (si : Fin (G.numStrats i)) (M : ℝ) (_hM : 0 ≤ M)
    (hbound : ∀ j s, |G.payoff j s| ≤ M) :
    |deviationPayoff G σ i si| ≤ M := by
  -- Let's denote the sum inside the absolute value by S.
  set S := ∑ s : (∀ j : Fin G.numPlayers, Fin (G.numStrats j)),
    (∏ j : Fin G.numPlayers,
      if h : j = i then
        if s j = h ▸ si then 1 else 0
      else (σ j).prob (s j)) * G.payoff i s;
  -- The sum S is bounded by M since each term in the sum is bounded by M.
  have hS_bound : |S| ≤ M * ∑ s : (∀ j : Fin G.numPlayers, Fin (G.numStrats j)),
    (∏ j : Fin G.numPlayers,
      if h : j = i then
        if s j = h ▸ si then 1 else 0
      else (σ j).prob (s j)) := by
        rw [ Finset.mul_sum _ _ _ ];
        exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun _ _ => by rw [ abs_le ] ; constructor <;> nlinarith [ abs_le.mp ( hbound i ‹_› ), show 0 ≤ ∏ j : Fin G.numPlayers, ( if h : j = i then if ‹∀ j : Fin G.numPlayers, Fin ( G.numStrats j ) › j = h ▸ si then 1 else 0 else ( σ j ).prob ( ‹∀ j : Fin G.numPlayers, Fin ( G.numStrats j ) › j ) ) from Finset.prod_nonneg fun _ _ => by split_ifs <;> linarith [ ( σ ‹_› ).nonneg ( ‹∀ j : Fin G.numPlayers, Fin ( G.numStrats j ) › ‹_› ) ] ] );
  -- The sum of the products over all s with s_i = si gives ∏_{j≠i} (∑ σ_j(s_j)) = 1.
  have h_prod_sum : ∑ s : (∀ j : Fin G.numPlayers, Fin (G.numStrats j)),
      (∏ j : Fin G.numPlayers,
        if h : j = i then
          if s j = h ▸ si then 1 else 0
        else (σ j).prob (s j)) = 1 := by
          have h_prod_sum : ∑ s : (∀ j : Fin G.numPlayers, Fin (G.numStrats j)),
              (∏ j : Fin G.numPlayers,
                if h : j = i then
                  if s j = h ▸ si then 1 else 0
                else (σ j).prob (s j)) = ∏ j : Fin G.numPlayers, ∑ s : Fin (G.numStrats j), (if h : j = i then if s = h ▸ si then 1 else 0 else (σ j).prob s) := by
                  exact Eq.symm (Fintype.prod_sum fun i_1 j => if h : i_1 = i then if j = Eq.symm h ▸ si then 1 else 0 else (σ i_1).prob j)
          rw [ h_prod_sum, Finset.prod_eq_one ];
          intro j hj; by_cases h : j = i <;> simp +decide [ h, ( σ j ).sum_one ] ;
  aesop
