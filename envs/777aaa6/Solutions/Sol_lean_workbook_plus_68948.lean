-- Prove2me | solution 1 for lean_workbook_plus_68948
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:46:20.607549+00:00
-- url     : https://prove2.me/submissions/1330c976-30fc-40c4-8138-69dcfe02324f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (z1 z2 z3 : ℂ) :
    ‖z1 - z2‖ ^ 2 + ‖z2 - z3‖ ^ 2 + ‖z3 - z1‖ ^ 2 + ‖z1 + z2 + z3‖ ^ 2 =
      3 * (‖z1‖ ^ 2 + ‖z2‖ ^ 2 + ‖z3‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im]
  ring

#print axioms solution
