-- Prove2me | solution 1 for BookSixth.shannon_entropy_le_log_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T06:05:26.606162+00:00
-- url     : https://prove2.me/submissions/9e0b31d4-4190-4282-b458-b01c630bc180

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (α : Type*) [Fintype α] [Nonempty α] (p : α → ℝ)
    (hnn : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    -∑ a, p a * Real.log (p a) ≤ Real.log (Fintype.card α) := by
  classical
  set S : Finset α := Finset.univ.filter (fun a => p a ≠ 0) with hS
  have hsupp : ∀ a ∈ S, 0 < p a := by
    intro a ha
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact lt_of_le_of_ne' (hnn a) ha
  have hsumS : ∑ a ∈ S, p a = 1 := by
    have hsub : ∑ a ∈ S, p a = ∑ a, p a := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro a _ haS
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at haS
      simp [haS]
    rw [hsub, hsum]
  have hconc : ConcaveOn ℝ (Set.Ioi 0) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have hJ := hconc.le_map_sum (t := S) (w := p)
    (p := fun a => (p a)⁻¹) (fun a _ => hnn a) hsumS
    (fun a ha => Set.mem_Ioi.mpr (inv_pos.mpr (hsupp a ha)))
  simp only [smul_eq_mul, Real.log_inv] at hJ
  have hsupp1 : ∀ a ∈ S, p a * (p a)⁻¹ = 1 :=
    fun a ha => mul_inv_cancel₀ (ne_of_gt (hsupp a ha))
  have hcard_sum : ∑ a ∈ S, p a * (p a)⁻¹ = (S.card : ℝ) := by
    trans ∑ _a ∈ S, (1 : ℝ)
    · exact Finset.sum_congr rfl (fun a ha => hsupp1 a ha)
    · simp
  have hLHS : ∑ a ∈ S, p a * (-Real.log (p a)) = -∑ a, p a * Real.log (p a) := by
    have e1 : ∑ a ∈ S, p a * (-Real.log (p a)) = ∑ a ∈ S, -(p a * Real.log (p a)) :=
      Finset.sum_congr rfl (fun a _ => mul_neg _ _)
    have e2 : ∑ a ∈ S, -(p a * Real.log (p a)) = -∑ a ∈ S, p a * Real.log (p a) :=
      Finset.sum_neg_distrib _
    have e3 : ∑ a ∈ S, p a * Real.log (p a) = ∑ a, p a * Real.log (p a) :=
      Finset.sum_subset (Finset.subset_univ S) (fun a _ haS => by
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at haS
        simp [haS])
    rw [e1, e2, e3]
  rw [hcard_sum] at hJ
  rw [hLHS] at hJ
  have hcardS : S.card ≤ Fintype.card α := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ S)
  have hSne : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    simp [hemp] at hsumS
  have hpos : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hSne
  calc -∑ a, p a * Real.log (p a) ≤ Real.log (S.card : ℝ) := hJ
    _ ≤ Real.log (Fintype.card α) :=
        Real.log_le_log hpos (by exact_mod_cast hcardS)
