-- Prove2me | solution 1 for lean_workbook_plus_80302
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:32:15.633023+00:00
-- url     : https://prove2.me/submissions/fc0d4e39-28a5-47bb-b97c-f8b2f49b5fc9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution : ¬ (∀ x y : ℤ,
    x^3 + y^3 + (-x * y)^3 - 3 * x * y * (-x * y) = 0) := by
  intro h
  have hbad := h 1 0
  norm_num at hbad
