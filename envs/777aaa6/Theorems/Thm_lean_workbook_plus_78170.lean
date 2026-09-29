-- Prove2me | Theorems.Thm_lean_workbook_plus_78170
-- name    : lean_workbook_plus_78170
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/490824ab-5aa4-44c9-a417-006d6edb1b1e
-- statement:
--   Adding: $T = 1 - \frac{\tan 46 + \tan 14}{\sqrt{3}}+1 + \frac{\tan 74 + \tan 46}{\sqrt{3}}-\frac{\tan 74 - \tan 14}{\sqrt{3}}+1=3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78170 : (1 - (Real.tan 46 + Real.tan 14) / Real.sqrt 3 + 1 + (Real.tan 74 + Real.tan 46) / Real.sqrt 3 - (Real.tan 74 - Real.tan 14) / Real.sqrt 3 + 1) = 3   :=  by sorry
