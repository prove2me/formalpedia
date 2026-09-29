-- Prove2me | Theorems.Thm_lean_workbook_plus_64830
-- name    : lean_workbook_plus_64830
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/043a2212-636b-45fc-b785-49aaa34cd59b
-- statement:
--   It is de Moivre's Formula: $x^{4}+y^{4}+z^{4}-2x^{2}y^{2}-2x^{2}z^{2}-2y^{2}z^{2}=-(x+y+z)(x+y-z)(-x+y+z)(x-y+z)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64830 (x y z : ℂ) : x^4 + y^4 + z^4 - 2 * x^2 * y^2 - 2 * x^2 * z^2 - 2 * y^2 * z^2 = -(x + y + z) * (x + y - z) * (-x + y + z) * (x - y + z)   :=  by sorry
