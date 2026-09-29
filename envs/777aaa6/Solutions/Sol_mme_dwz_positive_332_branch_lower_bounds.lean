-- Prove2me | solution 1 for mme_dwz_positive_332_branch_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T17:36:56.438689+00:00
-- url     : https://prove2.me/submissions/99978287-0863-451e-b0d5-65282a8f0751

import Definitions.Def_mme_dwz_positive_332_entropy_certificate_data
import Theorems.Thm_mme_dwz_positive_332_log_intervals

open BigOperators MME MME.RecursiveYZ MME.DWZ332Fine MME.DWZ332Certificate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem interval_term (q : ℚ) (h : Covered q) :
    (lowerTerm q : ℝ) ≤ Real.negMulLog (q : ℝ) ∧
    Real.negMulLog (q : ℝ) ≤ (upperTerm q : ℝ) := by
  rcases h with h | h | h
  · subst q; norm_num [lowerTerm, upperTerm]
  · subst q; norm_num [lowerTerm, upperTerm]
  · by_cases hz : q = 0 ∨ q = 1
    · rcases hz with hz | hz <;> subst q <;> norm_num [lowerTerm, upperTerm]
    have hl := mme_dwz_positive_332_log_intervals (logIndex q)
    rw [h] at hl
    have hq : (0 : ℝ) ≤ q := by
      have hall : ∀ j, 0 ≤ (certificates j).q := by decide +kernel
      exact_mod_cast h ▸ hall (logIndex q)
    simp only [lowerTerm, upperTerm, if_neg hz]
    push_cast
    simp only [Real.negMulLog_def]
    constructor
    · exact mul_le_mul_of_nonpos_left hl.2 (neg_nonpos.mpr hq)
    · exact mul_le_mul_of_nonpos_left hl.1 (neg_nonpos.mpr hq)

private theorem weights_nonneg : ∀ r, (0 : ℝ) ≤ weight r := by
  have h : ∀ r, (0 : ℚ) ≤ weight r := by decide +kernel
  intro r; exact_mod_cast h r

private theorem coverage_coarse : ∀ r g, Covered (coarse r 0 g) := by decide +kernel
private theorem coverage_parent : ∀ i : Fin 2, ∀ r a b, Covered (jointWord r (yzMode i) a b) := by decide +kernel
private theorem coverage_parts : ∀ i r s,
    (∀ w : Fin 9, w ≠ 0 → partMass i r s w = 0) ∨
      ((∀ w, Covered (partMass i r s w)) ∧ Covered (∑ w, partMass i r s w)) := by
  decide +kernel

private theorem bounds_order (q : ℚ) (hq : 0 ≤ q) : lowerTerm q ≤ upperTerm q := by
  have hc : ∀ j, (certificates j).lo ≤ (certificates j).hi := by decide +kernel
  unfold lowerTerm upperTerm
  split_ifs
  · rfl
  · exact mul_le_mul_of_nonpos_left (hc _) (neg_nonpos.mpr hq)

private theorem part_upper (i : Fin 2) (r : Fin 6) (s : Fin 15) :
    ratMassEntropy (partMass i r s) ≤
      (((∑ w, upperTerm (partMass i r s w)) - lowerTerm (∑ w, partMass i r s w) : ℚ) : ℝ) := by
  rcases coverage_parts i r s with hsingle | hc
  · have hmass : (∑ w, partMass i r s w) = partMass i r s 0 := by
      apply Finset.sum_eq_single 0
      · intro w hw hne; exact hsingle w hne
      · simp
    have hentropy : ratEntropy (partMass i r s) = Real.negMulLog (partMass i r s 0 : ℝ) := by
      unfold ratEntropy
      apply Finset.sum_eq_single 0
      · intro w hw hne; rw [hsingle w hne]; norm_num
      · simp
    have hupper : (∑ w, upperTerm (partMass i r s w)) = upperTerm (partMass i r s 0) := by
      apply Finset.sum_eq_single 0
      · intro w hw hne; rw [hsingle w hne]; norm_num [upperTerm]
      · simp
    rw [ratMassEntropy, hentropy, hmass, sub_self, hupper]
    have hpos : ∀ i r s w, 0 ≤ partMass i r s w := by decide +kernel
    exact_mod_cast sub_nonneg.mpr (bounds_order _ (hpos i r s 0))
  · unfold ratMassEntropy ratEntropy
    push_cast
    apply sub_le_sub
    · apply Finset.sum_le_sum
      intro w hw
      exact (interval_term _ (hc.1 w)).2
    · simpa only [Rat.cast_sum] using (interval_term _ hc.2).1

private theorem coarse_bound : (coarseLower : ℝ) ≤ coarseRate := by
  unfold coarseLower coarseRate ratEntropy
  push_cast
  apply Finset.sum_le_sum
  intro r hr
  apply mul_le_mul_of_nonneg_left _ (weights_nonneg r)
  apply Finset.sum_le_sum
  intro g hg
  exact (interval_term _ (coverage_coarse r g)).1

private theorem parent_bound (i : Fin 2) : (parentLower (yzMode i) : ℝ) ≤ parentRate (yzMode i) := by
  unfold parentLower parentRate
  push_cast
  apply Finset.sum_le_sum
  intro r hr
  apply mul_le_mul_of_nonneg_left _ (weights_nonneg r)
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  exact (interval_term _ (coverage_parent i r a b)).1

private theorem compatibility_bound (i : Fin 2) : compatibilityRate i ≤ (compatibilityUpper i : ℝ) := by
  unfold compatibilityRate compatibilityUpper
  push_cast
  apply Finset.sum_le_sum
  intro r hr
  apply mul_le_mul_of_nonneg_left _ (weights_nonneg r)
  apply Finset.sum_le_sum
  intro s hs
  simpa only [Rat.cast_sub, Rat.cast_sum] using part_upper i r s

private theorem coverage_alpha : ∀ r j, Covered (alpha r j) := by decide +kernel

private theorem penalty_bound : penaltyRate ≤ (penaltyUpper : ℝ) := by
  unfold penaltyRate penaltyUpper
  push_cast
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_left _ (weights_nonneg r)
  apply sub_le_sub_left
  unfold ratEntropy
  apply Finset.sum_le_sum
  intro j _
  exact (interval_term _ (coverage_alpha r j)).1

theorem solution :
    ((coarseLower : ℝ) - penaltyUpper ≤ coarseRate - penaltyRate) ∧
    ((parentLower 1 : ℝ) - compatibilityUpper 0 ≤ parentRate 1 - compatibilityRate 0) ∧
    ((parentLower 2 : ℝ) - compatibilityUpper 1 ≤ parentRate 2 - compatibilityRate 1) := by
  exact ⟨sub_le_sub coarse_bound penalty_bound, sub_le_sub (parent_bound 0) (compatibility_bound 0),
    sub_le_sub (parent_bound 1) (compatibility_bound 1)⟩
