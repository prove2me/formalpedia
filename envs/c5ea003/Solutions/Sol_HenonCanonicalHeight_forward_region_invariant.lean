-- Prove2me | solution 1 for HenonCanonicalHeight.forward_region_invariant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:52:12.872405+00:00
-- url     : https://prove2.me/submissions/8fa57aff-2082-4cd8-975f-efd3f8bdfbff

-- Sol generated from Bridges/HenonCanonicalHeight.lean
import Mathlib
import Definitions.Def_Bridges_HenonCanonicalHeight
import Theorems.Thm_HenonCanonicalHeight_forward_growth_bounds

/-!
# Escape regions and normalized heights for a Hénon map

This file formalizes algebraic and analytic ingredients used in the study of the map
`φ(x,y) = (y, x + y^D + b)`.  The escape region below is a slightly strengthened,
robust version of the usual archimedean escape region: the additional condition
`3 |y| < |y|^D` makes forward invariance transparent even in the presence of
cancellation.  No global arithmetic-height machinery is assumed.
-/

open HenonCanonicalHeight













open HenonCanonicalHeight in
theorem solution{D : ℕ} (hD : 2 ≤ D) {b : ℝ} {P : ℝ × ℝ}
    (hP : InForwardRegion D b P) :
    InForwardRegion D b (henon D b P) := by
  -- Let x = P.1, y = P.2
  set x := P.1 with hx
  set y := P.2 with hy
  -- Unfold definitions
  unfold henon InForwardRegion
  -- Get the original bounds
  have h1 : 3 * max (max |x| |b|) 1 < |y| ^ D := hP.1
  have h2 : 3 * |y| < |y| ^ D := hP.2
  -- This means |y| > 1
  have hy_one : |y| > 1 := by
    by_contra hc
    push_neg at hc
    have hy_nonneg : |y| ≥ 0 := abs_nonneg _
    have hyD_le_y : |y| ^ D ≤ |y| := by
      have hD1 : 1 ≤ D := by omega
      by_cases hy_eq_zero : |y| = 0
      · simp [hy_eq_zero, zero_pow (by omega : D ≠ 0)]
      · have hy_pos : |y| > 0 := lt_of_le_of_ne hy_nonneg (Ne.symm hy_eq_zero)
        calc |y| ^ D ≤ |y| ^ 2 := pow_le_pow_of_le_one hy_nonneg hc (by omega : D ≥ 2)
          _ = |y| * |y| := by ring
          _ ≤ |y| * 1 := by nlinarith
          _ = |y| := by ring
    linarith
  -- Apply forward_growth_bounds to get bounds on |x + y^D + b|
  have growth := forward_growth_bounds hP
  -- Let y' = x + y^D + b
  set y' := x + y ^ D + b with hy'_def
  -- We have (1/3) * |y|^D < |y'| < (5/3) * |y|^D
  have hy'_lower : (1/3 : ℝ) * |y| ^ D < |y'| := growth.1
  have hy'_upper : |y'| < (5/3 : ℝ) * |y| ^ D := growth.2
  -- From h2 and D ≥ 2, we get |y|^D > |y|, so (1/3)|y|^D > |y|/3 * 3 = |y| is not quite right
  -- Actually: |y|^D > 3|y| (from h2), so (1/3)|y|^D > |y|
  have hy'_gt_y : |y'| > |y| := by linarith
  -- Since |y| > 1, we have |y'| > 1
  have hy'_one : |y'| > 1 := by linarith
  -- Simplify the goal: (P.2, y').1 = y and (P.2, y').2 = y'
  simp
  -- Need to prove: 3 * max (max |y| |b|) 1 < |y'|^D ∧ 3 * |y'| < |y'|^D
  have key : |y| ^ D < |y'| ^ D := by
    gcongr
  -- Each component of max (max |y| |b|) 1 is < |y|^D / 3
  have hy_bound : |y| < |y|^D / 3 := by linarith
  have hb_bound : |b| < |y|^D / 3 := by linarith [le_max_right |x| |b|, le_max_left (max |x| |b|) 1]
  have h1_bound : 1 < |y|^D / 3 := by
    have : |y|^D > 1 := one_lt_pow₀ hy_one (by omega : D ≠ 0)
    linarith
  have hmax_lt : max (max |y| |b|) 1 < |y|^D / 3 := by
    apply max_lt <;> [apply max_lt; linarith] <;> linarith
  have h1' : 3 * max (max |y| |b|) 1 < |y|^D := by linarith
  have h1'' : 3 * max (max |y| |b|) 1 < |y'|^D := by linarith
  constructor
  · exact h1''
  · -- Second condition: 3 * |y'| < |y'|^D
    have hy_pos : |y| > 0 := by linarith
    have hy_Dm1 : |y| ^ (D - 1) > 3 := by
      have h2' : |y| ^ D > 3 * |y| := h2
      have hDeq : D = (D - 1) + 1 := by omega
      rw [hDeq, pow_succ] at h2'
      nlinarith
    have hy'_Dm1 : |y'| ^ (D - 1) > 3 := by
      have hy_abs_nonneg : |y| ≥ 0 := abs_nonneg _
      have hDm1_ne : D - 1 ≠ 0 := by omega
      calc |y'| ^ (D - 1) > |y| ^ (D - 1) := by gcongr
        _ > 3 := hy_Dm1
    have hD_eq : D = (D - 1) + 1 := by omega
    rw [hD_eq, pow_succ]
    nlinarith [abs_nonneg y']
