-- Prove2me | solution 1 for MarkovEntanglement.local_transition_deviation_mu_le_two_entanglement
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T17:34:18.551195+00:00
-- url     : https://prove2.me/submissions/0738d661-1d78-48d7-aac6-224c013a79cb

import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (μ : Joint S → ℝ) (hμ : IsPositiveDist μ) (hstat : IsStationary P μ) (i : Fin N)
    (Pi Ptrue : Matrix (S i) (S i) ℝ)
    (hPi : IsTransitionMatrix Pi)
    (hopt : muAgentTVDistN i μ P Pi = entanglementN i μ P)
    (hPtrue : IsTransitionMatrix Ptrue) (htrue : IsLocalTransitionN i P μ Ptrue) :
    muTVDist (marginalDist i μ) Ptrue Pi ≤ 2 * entanglementN i μ P := by
  classical
  have hμ0 : ∀ p, 0 ≤ μ p := fun p => (hμ.1 p).le
  have hm0 : ∀ s : S i, 0 ≤ marginalDist i μ s := by
    intro s
    refine Finset.sum_nonneg (fun q _ => ?_)
    by_cases h : q i = s
    · simp [h, hμ0 q]
    · simp [h]
  have key : ∀ s t : S i,
      marginalDist i μ s * |Ptrue s t - Pi s t|
        ≤ ∑ p : Joint S,
            (if p i = s then μ p * |marginalN i P p t - Pi (p i) t| else 0) := by
    intro s t
    have h2 : marginalDist i μ s * Pi s t
        = ∑ p : Joint S, (if p i = s then μ p * Pi (p i) t else 0) := by
      rw [marginalDist, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases h : p i = s <;> simp [h]
    have hEq : marginalDist i μ s * (Ptrue s t - Pi s t)
        = ∑ p : Joint S,
            (if p i = s then μ p * (marginalN i P p t - Pi (p i) t) else 0) := by
      rw [mul_sub, htrue s t, h2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases h : p i = s
      · simp [h]; ring
      · simp [h]
    calc marginalDist i μ s * |Ptrue s t - Pi s t|
        = |marginalDist i μ s * (Ptrue s t - Pi s t)| := by
          rw [abs_mul, abs_of_nonneg (hm0 s)]
      _ = |∑ p : Joint S,
            (if p i = s then μ p * (marginalN i P p t - Pi (p i) t) else 0)| := by rw [hEq]
      _ ≤ ∑ p : Joint S,
            |(if p i = s then μ p * (marginalN i P p t - Pi (p i) t) else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ p : Joint S,
            (if p i = s then μ p * |marginalN i P p t - Pi (p i) t| else 0) := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          by_cases h : p i = s
          · simp [h, abs_mul, abs_of_nonneg (hμ0 p)]
          · simp [h]
  have main : ∑ s : S i, marginalDist i μ s * ∑ t : S i, |Ptrue s t - Pi s t|
      ≤ ∑ p : Joint S, μ p * ∑ t : S i, |marginalN i P p t - Pi (p i) t| := by
    calc ∑ s : S i, marginalDist i μ s * ∑ t : S i, |Ptrue s t - Pi s t|
        ≤ ∑ s : S i, ∑ t : S i, ∑ p : Joint S,
            (if p i = s then μ p * |marginalN i P p t - Pi (p i) t| else 0) := by
          refine Finset.sum_le_sum (fun s _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum (fun t _ => key s t)
      _ = ∑ t : S i, ∑ p : Joint S, μ p * |marginalN i P p t - Pi (p i) t| := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          simp
      _ = ∑ p : Joint S, μ p * ∑ t : S i, |marginalN i P p t - Pi (p i) t| := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun p _ => (Finset.mul_sum _ _ _).symm)
  have hE0 : 0 ≤ entanglementN i μ P := by
    rw [← hopt, muAgentTVDistN]
    refine Finset.sum_nonneg (fun p _ => mul_nonneg (hμ0 p) ?_)
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg (fun t _ => abs_nonneg _))
  calc muTVDist (marginalDist i μ) Ptrue Pi
      = (1 / 2) * ∑ s : S i, marginalDist i μ s * ∑ t : S i, |Ptrue s t - Pi s t| := by
        rw [muTVDist, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun s _ => by ring)
    _ ≤ (1 / 2) * ∑ p : Joint S, μ p * ∑ t : S i, |marginalN i P p t - Pi (p i) t| :=
        mul_le_mul_of_nonneg_left main (by norm_num)
    _ = muAgentTVDistN i μ P Pi := by
        rw [muAgentTVDistN, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by ring)
    _ = entanglementN i μ P := hopt
    _ ≤ 2 * entanglementN i μ P := by linarith
