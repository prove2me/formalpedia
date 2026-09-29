-- Prove2me | solution 1 for MarkovEntanglement.local_transition_deviation_le_two_atv_entanglement
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T17:34:19.604449+00:00
-- url     : https://prove2.me/submissions/6122735b-9f4e-4661-8a31-4c8e2cb8aa9a

import Definitions.Def_markov_entanglement_multi_atv

open scoped BigOperators
open MarkovEntanglement

theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (μ : Joint S → ℝ) (hμ : IsPositiveDist μ) (hstat : IsStationary P μ) (i : Fin N)
    (Pi Ptrue : Matrix (S i) (S i) ℝ)
    (hPi : IsTransitionMatrix Pi)
    (hopt : agentTVDistN i P Pi = agentEntanglementWith i (agentTVDistN i) P)
    (hPtrue : IsTransitionMatrix Ptrue) (htrue : IsLocalTransitionN i P μ Ptrue) :
    ∀ s t, |Ptrue s t - Pi s t| ≤ 2 * agentEntanglementWith i (agentTVDistN i) P := by
  classical
  have hμ0 : ∀ p, 0 ≤ μ p := fun p => (hμ.1 p).le
  rw [← hopt]
  intro s t
  set A := agentTVDistN i P Pi with hA
  -- every entry of every marginalised row is within `2 A` of the candidate row
  have hbdd : BddAbove (Set.range (fun p : Joint S =>
      (1 / 2) * ∑ t : S i, |marginalN i P p t - Pi (p i) t|)) :=
    Set.Finite.bddAbove (Set.finite_range _)
  have hle : ∀ (p : Joint S) (t' : S i),
      |marginalN i P p t' - Pi (p i) t'| ≤ 2 * A := by
    intro p t'
    have h1 : (1 / 2) * ∑ t'' : S i, |marginalN i P p t'' - Pi (p i) t''| ≤ A :=
      le_ciSup hbdd p
    have h2 : |marginalN i P p t' - Pi (p i) t'|
        ≤ ∑ t'' : S i, |marginalN i P p t'' - Pi (p i) t''| :=
      Finset.single_le_sum (f := fun t'' => |marginalN i P p t'' - Pi (p i) t''|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ t')
    linarith
  -- the marginal of `μ` at `s` is strictly positive
  have hne : Nonempty (Joint S) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h := hμ.2
    simp at h
  obtain ⟨p0⟩ := hne
  have hp1i : (Function.update p0 i s) i = s := Function.update_self i s p0
  have hms : 0 < marginalDist i μ s := by
    have hb : (if (Function.update p0 i s) i = s then μ (Function.update p0 i s) else 0)
        ≤ marginalDist i μ s := by
      refine Finset.single_le_sum
        (f := fun q : Joint S => if q i = s then μ q else 0) ?_ (Finset.mem_univ _)
      intro q _
      by_cases h : q i = s <;> simp [h, hμ0 q]
    rw [if_pos hp1i] at hb
    exact lt_of_lt_of_le (hμ.1 _) hb
  -- weighted deviation bound
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
  have hchain : marginalDist i μ s * |Ptrue s t - Pi s t|
      ≤ marginalDist i μ s * (2 * A) := by
    calc marginalDist i μ s * |Ptrue s t - Pi s t|
        = |marginalDist i μ s * (Ptrue s t - Pi s t)| := by
          rw [abs_mul, abs_of_nonneg hms.le]
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
      _ ≤ ∑ p : Joint S, (if p i = s then μ p * (2 * A) else 0) := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          by_cases h : p i = s
          · simp only [if_pos h]
            exact mul_le_mul_of_nonneg_left (hle p t) (hμ0 p)
          · simp [h]
      _ = marginalDist i μ s * (2 * A) := by
          rw [marginalDist, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          by_cases h : p i = s <;> simp [h]
  exact le_of_mul_le_mul_left hchain hms
