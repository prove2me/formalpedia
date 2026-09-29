-- Prove2me | Theorems.Thm_lean_workbook_plus_79951
-- name    : lean_workbook_plus_79951
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e34dbdd9-bd92-4614-a79d-bcaf3b2eac8d
-- statement:
--   $(a+b+c+d)^2-8(ac+bd)=(a+b-c-d)^2-4(a-b)(c-d)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79951 (a b c d : ℝ) : (a + b + c + d) ^ 2 - 8 * (a * c + b * d) = (a + b - c - d) ^ 2 - 4 * (a - b) * (c - d)   :=  by sorry
