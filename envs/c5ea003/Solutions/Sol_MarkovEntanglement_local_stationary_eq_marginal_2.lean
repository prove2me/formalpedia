-- Prove2me | solution 2 for MarkovEntanglement.local_stationary_eq_marginal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T15:32:19.273109+00:00
-- url     : https://prove2.me/submissions/51374832-d804-4e4f-b36f-6d03823d2b6d

import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (μ : Joint S → ℝ) (hμ : IsPositiveDist μ) (hstat : IsStationary P μ)
    (i : Fin N) (Pi : Matrix (S i) (S i) ℝ)
    (hPi : IsLocalTransitionN i P μ Pi) :
    IsStationary Pi (marginalDist i μ) := by
  classical
  intro t
  calc ∑ s : S i, marginalDist i μ s * Pi s t
      = ∑ s : S i, ∑ p : Joint S, (if p i = s then μ p else 0) * marginalN i P p t :=
        Finset.sum_congr rfl (fun s _ => hPi s t)
    _ = ∑ p : Joint S, μ p * marginalN i P p t := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [← Finset.sum_mul]
        congr 1
        simp
    _ = ∑ q : Joint S, (if q i = t then μ q else 0) := by
        simp only [marginalN, Finset.mul_sum, mul_ite, mul_zero]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        by_cases h : q i = t
        · simp only [if_pos h]
          exact hstat q
        · simp [h]
    _ = marginalDist i μ t := rfl
