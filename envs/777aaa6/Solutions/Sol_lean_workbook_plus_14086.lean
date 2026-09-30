-- Prove2me | solution 1 for lean_workbook_plus_14086
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:58:51.606151+00:00
-- url     : https://prove2.me/submissions/2436ff34-84b8-4380-a38d-c93764f5383b

import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable def smoothDiskPlateau (p : ℝ × ℝ) : ℝ :=
  5 + expNegInvGlue (p.1 ^ 2 + p.2 ^ 2 - 1)

theorem smooth_disk_plateau_contDiff (n : ℕ∞) : ContDiff ℝ n smoothDiskPlateau := by
  exact contDiff_const.add (expNegInvGlue.contDiff.comp
    (((contDiff_fst.pow 2).add (contDiff_snd.pow 2)).sub contDiff_const))

theorem smooth_disk_plateau_continuous : Continuous smoothDiskPlateau :=
  (smooth_disk_plateau_contDiff ⊤).continuous

theorem smooth_disk_plateau_level_set (p : ℝ × ℝ) :
    smoothDiskPlateau p = 5 ↔ p.1 ^ 2 + p.2 ^ 2 ≤ 1 := by
  unfold smoothDiskPlateau
  rw [add_eq_left, expNegInvGlue.zero_iff_nonpos, sub_nonpos]

theorem smooth_disk_plateau_above_outside (p : ℝ × ℝ)
    (hp : 1 < p.1 ^ 2 + p.2 ^ 2) : 5 < smoothDiskPlateau p := by
  exact lt_add_of_pos_right 5 (expNegInvGlue.pos_of_pos (sub_pos.mpr hp))

theorem smooth_disk_plateau_not_constant :
    ¬ ∀ x y : ℝ × ℝ, smoothDiskPlateau x = smoothDiskPlateau y := by
  intro h
  have hzero : smoothDiskPlateau (0, 0) = 5 :=
    (smooth_disk_plateau_level_set _).mpr (by norm_num)
  have htwo : 5 < smoothDiskPlateau (2, 0) :=
    smooth_disk_plateau_above_outside _ (by norm_num)
  have he := h (0, 0) (2, 0)
  linarith

theorem smooth_nonconstant_disk_plateau_exists :
    ∃ f : ℝ × ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ Continuous f ∧
      (∀ p : ℝ × ℝ, f p = 5 ↔ p.1 ^ 2 + p.2 ^ 2 ≤ 1) ∧
      ¬ ∀ x y : ℝ × ℝ, f x = f y :=
  ⟨smoothDiskPlateau, smooth_disk_plateau_contDiff ⊤, smooth_disk_plateau_continuous,
    smooth_disk_plateau_level_set, smooth_disk_plateau_not_constant⟩

theorem solution : ¬ (¬ ∃ f : ℝ × ℝ → ℝ,
    (∀ x : ℝ × ℝ, x.fst ^ 2 + x.snd ^ 2 < 1 → f x = 5) ∧
      ¬ ∀ x y : ℝ × ℝ, f x = f y) := by
  intro h
  apply h
  refine ⟨smoothDiskPlateau, ?_, smooth_disk_plateau_not_constant⟩
  intro x hx
  exact (smooth_disk_plateau_level_set x).mpr hx.le

#print axioms smooth_disk_plateau_contDiff
#print axioms smooth_disk_plateau_continuous
#print axioms smooth_disk_plateau_level_set
#print axioms smooth_disk_plateau_above_outside
#print axioms smooth_disk_plateau_not_constant
#print axioms smooth_nonconstant_disk_plateau_exists
#print axioms solution
