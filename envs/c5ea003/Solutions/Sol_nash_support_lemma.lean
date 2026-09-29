-- Prove2me | solution 1 for nash_support_lemma
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:19:50.859237+00:00
-- url     : https://prove2.me/submissions/b85a8805-bf15-4cfe-9607-fc037b7e779c

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


theorem solution(G : FiniteGame) (σ : MixedProfile G)
    (hNash : IsNashEquilibrium G σ)
    (i : Fin G.numPlayers) (si : Fin (G.numStrats i))
    (hpos : 0 < (σ i).prob si) :
    deviationPayoff G σ i si = expectedPayoff G σ i := by
  by_contra h_contra;
  -- By definition of expected payoff, we have:
  have h_exp : expectedPayoff G σ i = ∑ si' : Fin (G.numStrats i), (σ i).prob si' * deviationPayoff G σ i si' := by
    unfold expectedPayoff deviationPayoff;
    simp +decide [ Finset.mul_sum _ _ _, Finset.sum_mul, Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
    rw [ Finset.sum_comm ];
    refine' Finset.sum_congr rfl fun y hy => _;
    rw [ Finset.sum_eq_single ( y i ) ] <;> simp_all +decide [ Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
    · rw [ ← mul_assoc, ← Finset.prod_erase_mul _ _ ( Finset.mem_univ i ) ];
      rw [ ← Finset.prod_erase_mul _ _ ( Finset.mem_univ i ) ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.prod_ite, Finset.filter_ne', Finset.filter_eq' ];
      exact Or.inl <| Or.inl <| Finset.prod_congr rfl fun x hx => by aesop;
    · intro b hb; rw [ Finset.prod_eq_zero ( Finset.mem_univ i ) ] <;> aesop;
  -- Since $σ(si) > 0$, we can apply the definition of Nash equilibrium to get that $deviationPayoff G σ i si ≤ expectedPayoff G σ i$.
  have h_le : ∀ si' : Fin (G.numStrats i), deviationPayoff G σ i si' ≤ expectedPayoff G σ i := by
    exact fun si' => hNash i si';
  exact h_contra <| le_antisymm ( h_le _ ) <| by have := Finset.sum_lt_sum ( fun x _ => mul_le_mul_of_nonneg_left ( h_le x ) <| ( σ i ).nonneg x ) ⟨ si, Finset.mem_univ si, mul_lt_mul_of_pos_left ( lt_of_le_of_ne ( h_le si ) h_contra ) hpos ⟩ ; norm_num [ ← Finset.sum_mul _ _ _, ( σ i ).sum_one ] at * ; linarith;
