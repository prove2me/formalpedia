-- Prove2me | solution 1 for exists_pure_at_most_as_good
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:09:31.71122+00:00
-- url     : https://prove2.me/submissions/2c0d674f-6923-4f59-9134-2c94a2501339

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
theorem expectedPayoff_eq_weighted_sum (G : FiniteGame) (σ : MixedProfile G)
    (i : Fin G.numPlayers) :
    expectedPayoff G σ i =
    ∑ si : Fin (G.numStrats i), (σ i).prob si * deviationPayoff G σ i si := by
  unfold expectedPayoff deviationPayoff;
  simp +decide [ Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
  rw [ Finset.sum_comm ];
  refine' Finset.sum_congr rfl fun s _ => _;
  simp +decide [ ← mul_assoc, ← Finset.prod_erase_mul _ _ ( Finset.mem_univ i ), Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
  exact Or.inl ( by rw [ mul_comm ] ; exact congr_arg _ ( Finset.prod_congr rfl fun j hj => by aesop ) )

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
    (i : Fin G.numPlayers) :
    ∃ si : Fin (G.numStrats i),
      deviationPayoff G σ i si ≤ expectedPayoff G σ i := by
  by_contra h_contra
  push_neg at h_contra;
  have h_sum : ∑ si : Fin (G.numStrats i), (σ i).prob si * deviationPayoff G σ i si > ∑ si : Fin (G.numStrats i), (σ i).prob si * expectedPayoff G σ i := by
    apply Finset.sum_lt_sum;
    · exact fun si _ => mul_le_mul_of_nonneg_left ( le_of_lt ( h_contra si ) ) ( σ i |>.nonneg si );
    · -- Since $\sigma$ is a mixed strategy, there exists some $si$ such that $(\sigma i).prob si > 0$.
      obtain ⟨si, hsi⟩ : ∃ si : Fin (G.numStrats i), (σ i).prob si > 0 := by
        exact not_forall_not.mp fun h => by have := σ i |>.sum_one; exact absurd this ( by rw [ Finset.sum_eq_zero fun x _ => le_antisymm ( le_of_not_gt fun hx => h x hx ) ( σ i |>.nonneg x ) ] ; norm_num ) ;
      exact ⟨ si, Finset.mem_univ _, mul_lt_mul_of_pos_left ( h_contra si ) hsi ⟩;
  simp_all +decide [ ← Finset.sum_mul _ _ _, expectedPayoff_eq_weighted_sum ];
  exact h_sum.ne ( by rw [ show ∑ si : Fin ( G.numStrats i ), ( σ i ).prob si = 1 from σ i |>.sum_one ] ; ring )
