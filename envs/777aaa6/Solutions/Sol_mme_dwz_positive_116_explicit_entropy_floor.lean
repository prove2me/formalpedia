-- Prove2me | solution 1 for mme_dwz_positive_116_explicit_entropy_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T17:43:29.32098+00:00
-- url     : https://prove2.me/submissions/aafa2c53-a956-49bb-8b6c-15a2072dfb30

import Definitions.Def_mme_dwz_positive_116_entropy_certificate_data
import Theorems.Thm_mme_dwz_positive_116_log_intervals

open BigOperators MME MME.RecursiveYZ MME.DWZ116Fine MME.DWZ116Certificate
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
    have hl := mme_dwz_positive_116_log_intervals (logIndex q)
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

private theorem part_upper (i : Fin 2) (r : Fin 6) (s : Fin 9) :
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

private theorem numerical_floor : ∀ i, (4622208849 / 10000000000 : ℚ) < rateLower i := by
  decide +kernel

theorem solution : (4622208849 / 10000000000 : ℝ) < explicitRate := by
  have h0 := numerical_floor 0
  have h1 := numerical_floor 1
  have h2 := numerical_floor 2
  change (4622208849 / 10000000000 : ℚ) < coarseLower at h0
  change (4622208849 / 10000000000 : ℚ) < parentLower 1 - compatibilityUpper 0 at h1
  change (4622208849 / 10000000000 : ℚ) < parentLower 2 - compatibilityUpper 1 at h2
  have hb1 := sub_le_sub (parent_bound 0) (compatibility_bound 0)
  have hb2 := sub_le_sub (parent_bound 1) (compatibility_bound 1)
  have hc0 : (4622208849 / 10000000000 : ℝ) < (coarseLower : ℝ) := by
    have h := Rat.cast_lt (K := ℝ) |>.mpr h0
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    exact h
  have hc1 : (4622208849 / 10000000000 : ℝ) < (parentLower 1 : ℝ) - compatibilityUpper 0 := by
    have h := Rat.cast_lt (K := ℝ) |>.mpr h1
    push_cast at h
    exact h
  have hc2 : (4622208849 / 10000000000 : ℝ) < (parentLower 2 : ℝ) - compatibilityUpper 1 := by
    have h := Rat.cast_lt (K := ℝ) |>.mpr h2
    push_cast at h
    exact h
  unfold explicitRate
  exact lt_min (hc0.trans_le coarse_bound) (lt_min (hc1.trans_le hb1) (hc2.trans_le hb2))
