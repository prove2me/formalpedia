-- Prove2me | solution 1 for BookSixth.fiber_entropy_le_log_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T09:04:45.552636+00:00
-- url     : https://prove2.me/submissions/f16a8d0e-25a4-4587-84fd-2809beeb85aa

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (β : Type*) [Fintype β] [Nonempty β] (w : β → ℝ)
    (S : Finset β) (P : ℝ) (hP : 0 < P) (hnn : ∀ b, 0 ≤ w b)
    (hsum : ∑ b, w b = P) (hsupp : ∀ b ∉ S, w b = 0) (hne : S.Nonempty) :
    -∑ b, w b * Real.log (w b / P) ≤ P * Real.log (S.card : ℝ) := by
  classical
  -- work over the effective support inside S
  set S' : Finset β := S.filter (fun b => w b ≠ 0) with hS'
  have hw0 : ∀ b ∉ S', w b = 0 := by
    intro b hb
    simp only [hS', Finset.mem_filter] at hb
    by_cases hSb : b ∈ S
    · by_contra hc
      exact hb ⟨hSb, hc⟩
    · exact hsupp b hSb
  have hS'ne : S'.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hall : ∀ b, w b = 0 := by
      intro b
      by_cases h : b ∈ S'
      · rw [hemp] at h
        simp at h
      · exact hw0 b h
    have hzero : ∑ b, w b = 0 := Finset.sum_eq_zero (fun b _ => hall b)
    have hP0 : P = 0 := by rw [← hsum]; exact hzero
    linarith
  have hpos : ∀ b ∈ S', 0 < w b := by
    intro b hb
    simp only [hS', Finset.mem_filter] at hb
    exact lt_of_le_of_ne' (hnn b) hb.2
  have hsumS' : ∑ b ∈ S', w b / P = 1 := by
    have hsub : ∑ b ∈ S', w b / P = ∑ b, w b / P := by
      apply Finset.sum_subset (Finset.subset_univ S')
      intro b _ hbS'
      simp [hw0 b hbS']
    rw [hsub, ← Finset.sum_div, hsum, div_self (ne_of_gt hP)]
  have hconc : ConcaveOn ℝ (Set.Ioi 0) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have hJ := hconc.le_map_sum (t := S') (w := fun b => w b / P)
    (p := fun b => (w b / P)⁻¹)
    (fun b _ => div_nonneg (hnn b) (le_of_lt hP)) hsumS'
    (fun b hb => Set.mem_Ioi.mpr
      (inv_pos.mpr (div_pos (hpos b hb) hP)))
  simp only [smul_eq_mul, Real.log_inv] at hJ
  have hcard_sum : ∑ b ∈ S', (w b / P) * (w b / P)⁻¹
      = (S'.card : ℝ) := by
    trans ∑ _b ∈ S', (1 : ℝ)
    · exact Finset.sum_congr rfl (fun b hb => mul_inv_cancel₀
        (ne_of_gt (div_pos (hpos b hb) hP)))
    · simp
  rw [hcard_sum] at hJ
  have e1 : ∑ b ∈ S', (w b / P) * (-Real.log (w b / P))
      = ∑ b ∈ S', -((w b / P) * Real.log (w b / P)) :=
    Finset.sum_congr rfl (fun b _ => mul_neg _ _)
  have e2 : ∑ b ∈ S', -((w b / P) * Real.log (w b / P))
      = -∑ b ∈ S', (w b / P) * Real.log (w b / P) :=
    Finset.sum_neg_distrib _
  have e4 : ∀ b ∈ S', (w b / P) * Real.log (w b / P)
      = P⁻¹ * (w b * Real.log (w b / P)) := by
    intro b _
    rw [div_eq_mul_inv]
    ring
  have e6 : ∑ b, w b * Real.log (w b / P)
      = ∑ b ∈ S', w b * Real.log (w b / P) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S')
    intro b _ hbS'
    simp [hw0 b hbS']
  have e5 : ∑ b ∈ S', (w b / P) * Real.log (w b / P)
      = P⁻¹ * (∑ b, w b * Real.log (w b / P)) := by
    calc ∑ b ∈ S', (w b / P) * Real.log (w b / P)
        = ∑ b ∈ S', P⁻¹ * (w b * Real.log (w b / P)) :=
          Finset.sum_congr rfl (fun b hb => e4 b hb)
      _ = P⁻¹ * (∑ b ∈ S', w b * Real.log (w b / P)) :=
          (Finset.mul_sum _ _ _).symm
      _ = P⁻¹ * (∑ b, w b * Real.log (w b / P)) := by
          rw [e6]
  have hLHS : ∑ b ∈ S', (w b / P) * (-Real.log (w b / P))
      = P⁻¹ * (-∑ b, w b * Real.log (w b / P)) := by
    rw [e1, e2, e5, e6, mul_neg]
  rw [hLHS] at hJ
  have hmul := mul_le_mul_of_nonneg_left hJ (le_of_lt hP)
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hP), one_mul] at hmul
  have hcardS : S'.card ≤ S.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hpos' : (0 : ℝ) < (S'.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS'ne
  have hble : Real.log (S'.card : ℝ) ≤ Real.log (S.card : ℝ) :=
    Real.log_le_log hpos' (by exact_mod_cast hcardS)
  exact hmul.trans
    (mul_le_mul_of_nonneg_left hble (le_of_lt hP))
