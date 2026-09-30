-- Prove2me | solution 1 for lean_workbook_plus_82004
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:46:28.851679+00:00
-- url     : https://prove2.me/submissions/2c83ee2b-fceb-4c74-87bb-8dd3091bca06

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (z w : ℂ) (h₁ : z + w = 8 + 6 * Complex.I) (h₂ : ‖z - w‖ = 4) :
    ‖z‖ ^ 2 + ‖w‖ ^ 2 = 58 := by
  have hpar : ‖z + w‖ ^ 2 + ‖z - w‖ ^ 2 = 2 * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im]
    ring
  have hsum : ‖z + w‖ ^ 2 = 100 := by
    rw [h₁]
    norm_num [Complex.sq_norm, Complex.normSq_apply]
  rw [h₂] at hpar
  linarith

#print axioms solution
