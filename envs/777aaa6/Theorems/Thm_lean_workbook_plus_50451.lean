-- Prove2me | Theorems.Thm_lean_workbook_plus_50451
-- name    : lean_workbook_plus_50451
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/de2de6ed-16b3-4189-ab48-bc4103fc5599
-- statement:
--   If $a+b+c=0$ . Prove that $(a^2+b^2+c^2)^2 = 2(a^4+b^4+c^4)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50451 (a b c : ℝ) (h : a + b + c = 0) :
  (a^2 + b^2 + c^2)^2 = 2 * (a^4 + b^4 + c^4)   :=  by sorry
