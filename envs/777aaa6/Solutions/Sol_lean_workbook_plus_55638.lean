-- Prove2me | solution 1 for lean_workbook_plus_55638
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:56:21.403599+00:00
-- url     : https://prove2.me/submissions/de03ca54-672c-42e2-acd3-69b8e67d3ef2

import Mathlib

namespace CubicIntervalExactRange

def value (p : ℝ) : ℝ := 3 * p ^ 3 + 3 * p ^ 2 - 3 * p

theorem gap_identities (p : ℝ) :
    value p + 6 = 3 * (p + 2) * (p ^ 2 - p + 1) ∧
      3 - value p = 3 * (1 - p) * (p + 1) ^ 2 := by
  constructor <;> unfold value <;> ring

theorem quadratic_pos (p : ℝ) : 0 < p ^ 2 - p + 1 := by
  nlinarith [sq_nonneg (p - 1 / 2)]

theorem bounds (p : ℝ) (hp : p ∈ Set.Icc (-2) (2 / 3 : ℝ)) :
    -6 ≤ value p ∧ value p ≤ 3 := by
  obtain ⟨hl, hu⟩ := gap_identities p
  have h1 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
    (by linarith [hp.1] : 0 ≤ p + 2)) (quadratic_pos p).le
  have h2 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
    (by linarith [hp.2] : 0 ≤ 1 - p)) (sq_nonneg (p + 1))
  constructor <;> linarith

theorem extremizers (p : ℝ) (hp : p ∈ Set.Icc (-2) (2 / 3 : ℝ)) :
    (value p = -6 ↔ p = -2) ∧ (value p = 3 ↔ p = -1) := by
  obtain ⟨hl, hu⟩ := gap_identities p
  constructor
  · constructor
    · intro h
      have hz : 3 * (p + 2) * (p ^ 2 - p + 1) = 0 := by linarith
      have hmul := (mul_eq_zero.mp hz).resolve_right (ne_of_gt (quadratic_pos p))
      linarith
    · rintro rfl
      unfold value
      ring
  · constructor
    · intro h
      have hpos : 0 < 3 * (1 - p) := by linarith [hp.2]
      have hz : 3 * (1 - p) * (p + 1) ^ 2 = 0 := by linarith
      have hsq := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hpos)
      have he := sq_eq_zero_iff.mp hsq
      linarith
    · rintro rfl
      unfold value
      ring

theorem continuous_value : Continuous value := by unfold value; fun_prop

theorem exact_image : value '' Set.Icc (-2) (2 / 3 : ℝ) = Set.Icc (-6) 3 := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact bounds p hp
  · intro hy
    have hleft : value (-2) = -6 := by unfold value; ring
    have hright : value (-1) = 3 := by unfold value; ring
    have hi := intermediate_value_Icc (by norm_num : (-2 : ℝ) ≤ -1)
      (continuous_value.continuousOn (s := Set.Icc (-2) (-1)))
    rw [hleft, hright] at hi
    obtain ⟨p, hp, hpy⟩ := hi hy
    exact ⟨p, ⟨hp.1, by linarith [hp.2]⟩, hpy⟩

theorem derivative_value (p : ℝ) :
    HasDerivAt value (3 * (p + 1) * (3 * p - 1)) p := by
  unfold value
  convert ((((hasDerivAt_id p).pow 3).const_mul 3).add
    (((hasDerivAt_id p).pow 2).const_mul 3)).sub
    ((hasDerivAt_id p).const_mul 3) using 1 <;> simp only [id_eq] <;> ring

theorem critical_points (p : ℝ) : deriv value p = 0 ↔ p = -1 ∨ p = 1 / 3 := by
  rw [(derivative_value p).deriv]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · left
      rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · linarith
    · right
      linarith
  · rintro (rfl | rfl) <;> ring

theorem graph_monotonicity :
    StrictMonoOn value (Set.Iic (-1)) ∧
      StrictAntiOn value (Set.Icc (-1) (1 / 3 : ℝ)) ∧
      StrictMonoOn value (Set.Ici (1 / 3 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Iic (-1)) continuous_value.continuousOn
    intro p hp
    rw [interior_Iic] at hp
    change p < -1 at hp
    rw [(derivative_value p).deriv]
    exact mul_pos_of_neg_of_neg (by linarith [hp] : 3 * (p + 1) < 0)
      (by linarith [hp] : 3 * p - 1 < 0)
  · apply strictAntiOn_of_deriv_neg (convex_Icc (-1) (1 / 3)) continuous_value.continuousOn
    intro p hp
    rw [interior_Icc] at hp
    change -1 < p ∧ p < 1 / 3 at hp
    rw [(derivative_value p).deriv]
    exact mul_neg_of_pos_of_neg (by linarith [hp.1] : 0 < 3 * (p + 1))
      (by linarith [hp.2] : 3 * p - 1 < 0)
  · apply strictMonoOn_of_deriv_pos (convex_Ici (1 / 3)) continuous_value.continuousOn
    intro p hp
    rw [interior_Ici] at hp
    change 1 / 3 < p at hp
    rw [(derivative_value p).deriv]
    exact mul_pos (by linarith [hp] : 0 < 3 * (p + 1))
      (by linarith [hp] : 0 < 3 * p - 1)

theorem graph_values :
    value (-2) = -6 ∧ value (-1) = 3 ∧
      value (1 / 3) = -5 / 9 ∧ value (2 / 3) = 2 / 9 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold value <;> ring

end CubicIntervalExactRange

theorem solution (p : ℝ) (hp : -2 ≤ p ∧ p ≤ 2 / 3) :
    -6 ≤ 3 * p ^ 3 + 3 * p ^ 2 - 3 * p ∧
      3 * p ^ 3 + 3 * p ^ 2 - 3 * p ≤ 6 := by
  have h := CubicIntervalExactRange.bounds p hp
  exact ⟨h.1, h.2.trans (by norm_num)⟩

#print axioms CubicIntervalExactRange.gap_identities
#print axioms CubicIntervalExactRange.bounds
#print axioms CubicIntervalExactRange.extremizers
#print axioms CubicIntervalExactRange.exact_image
#print axioms CubicIntervalExactRange.derivative_value
#print axioms CubicIntervalExactRange.critical_points
#print axioms CubicIntervalExactRange.graph_monotonicity
#print axioms CubicIntervalExactRange.graph_values
#print axioms solution
