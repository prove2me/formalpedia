-- Prove2me | solution 1 for lean_workbook_plus_79395
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:35:51.129019+00:00
-- url     : https://prove2.me/submissions/917e67e0-1c27-4195-b815-4c0695601de5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) :
    a*b*c*(a*b+b*c+c*a) ≤ a^3*b^2+b^3*c^2+c^3*a^2 ↔
    7*a^3*b^2+7*b^3*c^2+7*c^3*a^2 ≥ 7*(a^2*b^2*c+b^2*c^2*a+c^2*a^2*b) := by
  constructor <;> intro h <;> nlinarith only [h]
