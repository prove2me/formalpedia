-- Prove2me | solution 1 for HenonCanonicalHeight.backward_region_invariant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:48:33.801558+00:00
-- url     : https://prove2.me/submissions/f3a60ac1-5a06-4cd5-8f70-5bff504410a9

-- Sol generated from Bridges/HenonCanonicalHeight.lean
import Mathlib
import Definitions.Def_Bridges_HenonCanonicalHeight

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
    (hP : InBackwardRegion D b P) :
    InBackwardRegion D b (henonInv D b P) := by
  obtain ⟨h1, h2⟩ := hP
  simp [InBackwardRegion, henonInv] at *
  -- Let z = P.2 - P.1^D - b
  set z := P.2 - P.1 ^ D - b with hz_def
  -- Key bounds from h1
  have h1' : max (max |P.2| |b|) 1 < |P.1| ^ D / 3 := by linarith
  have hP2_bound : |P.2| < |P.1| ^ D / 3 := by
    calc |P.2| ≤ max |P.2| |b| := le_max_left _ _
      _ ≤ max (max |P.2| |b|) 1 := le_max_left _ _
      _ < |P.1| ^ D / 3 := h1'
  have hb_bound : |b| < |P.1| ^ D / 3 := by
    calc |b| ≤ max |P.2| |b| := le_max_right _ _
      _ ≤ max (max |P.2| |b|) 1 := le_max_left _ _
      _ < |P.1| ^ D / 3 := h1'
  -- |P.1|^D > 3 since max ≥ 1
  have hmax_ge_one : (1 : ℝ) ≤ max (max |P.2| |b|) 1 := le_max_right _ _
  have hPD_pos : (3 : ℝ) < |P.1| ^ D := by nlinarith
  have hPD_div3_pos : (1 : ℝ) < |P.1| ^ D / 3 := by linarith
  -- Lower bound on |z| using triangle inequality
  have hz_lower : |z| ≥ |P.1| ^ D - |P.2| - |b| := by
    have hz_eq : z = -(P.1 ^ D + (b - P.2)) := by simp [hz_def]; ring
    rw [hz_eq, abs_neg]
    have htri : |P.1 ^ D + (b - P.2)| ≥ |P.1 ^ D| - |b - P.2| := by
      have := abs_sub_abs_le_abs_add (P.1 ^ D) (b - P.2)
      linarith
    have htri2 : |b - P.2| ≤ |b| + |P.2| := abs_sub _ _
    have habs_pow : |P.1 ^ D| = |P.1| ^ D := abs_pow P.1 D
    calc |P.1 ^ D + (b - P.2)| ≥ |P.1 ^ D| - |b - P.2| := htri
      _ = |P.1|^D - |b - P.2| := by rw [habs_pow]
      _ ≥ |P.1|^D - (|b| + |P.2|) := by linarith [htri2]
      _ = |P.1| ^ D - |P.2| - |b| := by ring
  -- |z| > |P.1|^D / 3 > 1
  have hz_gt : |z| > |P.1| ^ D / 3 := by linarith
  have hz_gt1 : |z| > 1 := by linarith
  -- |z| > |P.1| since |P.1|^(D-1) > 3
  have heq_pow : |P.1| ^ D = |P.1| ^ (D - 1) * |P.1| := by
    rcases D with _ | _ | D <;> simp [pow_succ] at *
  have hP1_pos : 0 < |P.1| := by
    have hD_pos : D ≠ 0 := by linarith
    have h1_abs : |P.1| ≥ 0 := abs_nonneg _
    cases' lt_or_eq_of_le h1_abs with hpos heq
    · exact hpos
    · rw [heq.symm] at hPD_pos
      simp [hD_pos] at hPD_pos
      linarith
  have hPD_div3_gt_P1 : |P.1| ^ D / 3 > |P.1| := by
    have h2'_old : 3 < |P.1| ^ (D - 1) := by nlinarith [heq_pow, hP1_pos]
    rw [heq_pow]
    nlinarith [h2'_old]
  have hz_gt_P1 : |z| > |P.1| := by linarith
  have h2'_old : 3 < |P.1| ^ (D - 1) := by nlinarith [heq_pow, hP1_pos]
  -- |z|^(D-1) > |P.1|^(D-1) > 3
  have hD1 : D - 1 ≥ 1 := by omega
  have hz_sub : |z| ^ (D - 1) > |P.1| ^ (D - 1) := by gcongr
  have hz_pow_gt3 : 3 < |z| ^ (D - 1) := lt_trans h2'_old hz_sub
  -- |z|^D = |z| * |z|^(D-1)
  have heqz : |z| ^ D = |z| * |z| ^ (D - 1) := by
    have hD_eq : D = D - 1 + 1 := by omega
    conv_lhs => rw [hD_eq, pow_succ]
    ring
  -- Second part: 3 * |z| < |z|^D
  have h_part2 : 3 * |z| < |z| ^ D := by rw [heqz]; nlinarith
  -- First part: 3 * max (max |P.1| |b|) 1 < |z|^D
  have h_part1 : 3 * max (max |P.1| |b|) 1 < |z| ^ D := by
    have hb_le_z : |b| ≤ |z| := by linarith
    have hmax_le : max (max |P.1| |b|) 1 ≤ |z| := by
      have h1 : max |P.1| |b| ≤ |z| := le_trans (max_le_max hz_gt_P1.le le_rfl) (max_le le_rfl hb_le_z)
      exact max_le h1 hz_gt1.le
    nlinarith [h_part2]
  exact ⟨h_part1, h_part2⟩
