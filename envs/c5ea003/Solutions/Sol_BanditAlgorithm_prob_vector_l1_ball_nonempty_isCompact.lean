-- Prove2me | solution 1 for BanditAlgorithm.prob_vector_l1_ball_nonempty_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T16:35:54.89467+00:00
-- url     : https://prove2.me/submissions/2d638507-208d-4ed3-88ff-cc01a32124eb

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open Finset

/-!
The confidence set of UCRL2 — the probability vectors within `L¹` distance `β`
of the empirical transition row — is nonempty and compact.  Nonempty because it
contains the empirical row itself; compact because it is a closed subset of the
cube `[0,1]^ι`, a coordinatewise bound that follows from nonnegativity together
with the normalisation.
-/

theorem solution {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∑ i, c i = 1) (β : ℝ) (hβ : 0 ≤ β) :
    (∃ p : ι → ℝ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ ∑ i, |p i - c i| ≤ β) ∧
      IsCompact {p : ι → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ ∑ i, |p i - c i| ≤ β} := by
  constructor
  · refine ⟨c, hc0, hc1, ?_⟩
    simpa using hβ
  · have hclosed : IsClosed
        {p : ι → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ ∑ i, |p i - c i| ≤ β} := by
      have h1 : IsClosed {p : ι → ℝ | ∀ i, 0 ≤ p i} := by
        rw [Set.setOf_forall]
        exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
      have h2 : IsClosed {p : ι → ℝ | ∑ i, p i = 1} :=
        isClosed_eq (continuous_finset_sum _ fun i _ ↦ continuous_apply i) continuous_const
      have h3 : IsClosed {p : ι → ℝ | ∑ i, |p i - c i| ≤ β} :=
        isClosed_le (continuous_finset_sum _ fun i _ ↦
          ((continuous_apply i).sub continuous_const).abs) continuous_const
      have hsplit : {p : ι → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ ∑ i, |p i - c i| ≤ β}
          = {p : ι → ℝ | ∀ i, 0 ≤ p i} ∩
            ({p : ι → ℝ | ∑ i, p i = 1} ∩ {p : ι → ℝ | ∑ i, |p i - c i| ≤ β}) :=
        Set.ext fun _ ↦ Iff.rfl
      rw [hsplit]
      exact h1.inter (h2.inter h3)
    have hsub : {p : ι → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ ∑ i, |p i - c i| ≤ β}
        ⊆ Set.univ.pi fun _ : ι ↦ Set.Icc (0 : ℝ) 1 := by
      intro p hp i _
      refine ⟨hp.1 i, ?_⟩
      have h := Finset.single_le_sum (f := p) (fun j _ ↦ hp.1 j) (mem_univ i)
      rw [hp.2.1] at h
      exact h
    exact IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ ↦ isCompact_Icc) hclosed hsub
