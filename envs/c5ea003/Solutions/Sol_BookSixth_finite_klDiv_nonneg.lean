-- Prove2me | solution 1 for BookSixth.finite_klDiv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T06:16:19.509565+00:00
-- url     : https://prove2.me/submissions/5d496619-e401-49e1-83ae-f600a67b95f4

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (α : Type*) [Fintype α] [Nonempty α] (p q : α → ℝ)
    (hpn : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1)
    (hqn : ∀ a, 0 ≤ q a) (hqsum : ∑ a, q a = 1)
    (hsupp : ∀ a, p a ≠ 0 → q a ≠ 0) :
    0 ≤ ∑ a, p a * Real.log (p a / q a) := by
  classical
  set S : Finset α := Finset.univ.filter (fun a => p a ≠ 0) with hS
  have hsuppP : ∀ a ∈ S, 0 < p a := by
    intro a ha
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact lt_of_le_of_ne' (hpn a) ha
  have hsuppQ : ∀ a ∈ S, 0 < q a := by
    intro a ha
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact lt_of_le_of_ne' (hqn a) (hsupp a ha)
  have hsumS : ∑ a ∈ S, p a = 1 := by
    have hsub : ∑ a ∈ S, p a = ∑ a, p a := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro a _ haS
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at haS
      simp [haS]
    rw [hsub, hpsum]
  have hconc : ConcaveOn ℝ (Set.Ioi 0) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have hJ := hconc.le_map_sum (t := S) (w := p)
    (p := fun a => q a / p a) (fun a _ => hpn a) hsumS
    (fun a ha => Set.mem_Ioi.mpr (div_pos (hsuppQ a ha) (hsuppP a ha)))
  simp only [smul_eq_mul] at hJ
  have hcancel : ∀ a ∈ S, p a * (q a / p a) = q a :=
    fun a ha => mul_div_cancel₀ _ (ne_of_gt (hsuppP a ha))
  have hsumQ : ∑ a ∈ S, p a * (q a / p a) = ∑ a ∈ S, q a :=
    Finset.sum_congr rfl (fun a ha => hcancel a ha)
  have hsplit : ∀ a ∈ S, p a * Real.log (p a / q a)
      = p a * Real.log (p a) - p a * Real.log (q a) := by
    intro a ha
    rw [Real.log_div (ne_of_gt (hsuppP a ha)) (ne_of_gt (hsuppQ a ha)), mul_sub]
  have hgoal : ∑ a, p a * Real.log (p a / q a)
      = ∑ a ∈ S, p a * Real.log (p a) - ∑ a ∈ S, p a * Real.log (q a) := by
    have e1 : ∑ a, p a * Real.log (p a / q a) = ∑ a ∈ S, p a * Real.log (p a / q a) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro a _ haS
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at haS
      simp [haS]
    rw [e1, Finset.sum_congr rfl (fun a ha => hsplit a ha), Finset.sum_sub_distrib]
  have hQle : ∑ a ∈ S, q a ≤ 1 := by
    have hle : ∑ a ∈ S, q a ≤ ∑ a, q a :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun a _ _ => hqn a)
    rw [hqsum] at hle
    exact hle
  have hQpos : 0 < ∑ a ∈ S, q a := by
    apply Finset.sum_pos (fun a ha => hsuppQ a ha)
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    simp [hemp] at hsumS
  rw [hgoal]
  have hlog : Real.log (∑ a ∈ S, q a) ≤ 0 :=
    Real.log_nonpos (le_of_lt hQpos) hQle
  have hJ2 : ∑ a ∈ S, p a * Real.log (q a / p a) ≤ Real.log (∑ a ∈ S, q a) := by
    rw [← hsumQ]; exact hJ
  have hneg : ∑ a ∈ S, p a * Real.log (p a) - ∑ a ∈ S, p a * Real.log (q a)
      = -(∑ a ∈ S, p a * Real.log (q a / p a)) := by
    have e : ∀ a ∈ S, p a * Real.log (p a) - p a * Real.log (q a)
        = -(p a * Real.log (q a / p a)) := by
      intro a ha
      rw [Real.log_div (ne_of_gt (hsuppQ a ha)) (ne_of_gt (hsuppP a ha))]
      ring
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun a ha => e a ha),
      Finset.sum_neg_distrib]
  rw [hneg]
  exact neg_nonneg.mpr (le_trans hJ2 hlog)
