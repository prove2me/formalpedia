-- Prove2me | Theorems.Thm_lean_workbook_plus_81289
-- name    : lean_workbook_plus_81289
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/9d1190f5-cd82-4538-884e-f0e882350c86
-- statement:
--   Calculate the symmetric sum: $\sum_{cyc} 2ac = 2(ac+bd+ca+db) = 4(ac+bd)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81289 (a b c d : ℂ) : 2 * (a * c + b * d + c * a + d * b) = 4 * (a * c + b * d)   :=  by sorry
