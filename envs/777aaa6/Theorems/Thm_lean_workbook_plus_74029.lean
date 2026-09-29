-- Prove2me | Theorems.Thm_lean_workbook_plus_74029
-- name    : lean_workbook_plus_74029
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/952e8836-c56e-4e4e-8073-f2c76f82750c
-- statement:
--   Applying the quadratic formula again, find that that $z=\frac{6\pm\sqrt{36-4(3)(-9+4a)}}{2(3)}\implies z=\frac{6\pm\sqrt{144-48a}}{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74029 (a : ℝ) : (6 + Real.sqrt (36 - 4 * 3 * (-9 + 4 * a))) / (2 * 3) = (6 + Real.sqrt (144 - 48 * a)) / 6   :=  by sorry
