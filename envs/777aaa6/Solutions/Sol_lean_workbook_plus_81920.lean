-- Prove2me | solution 1 for lean_workbook_plus_81920
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:36:53.471038+00:00
-- url     : https://prove2.me/submissions/744edf5c-a27b-4771-a457-92296f338a60

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution : ¬ (∀ x y z : ℝ,
    x^2*y^2 + x^2*z^2 + y^2*z^2 - x*y*z*(x+y+z) ≥ 4.5*(1-x*y*z)) := by
  intro h
  have hbad := h 0 0 0
  norm_num at hbad
