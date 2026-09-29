-- Prove2me | Theorems.Thm_lean_workbook_plus_7988
-- name    : lean_workbook_plus_7988
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/8593f220-4019-4751-88ac-3c060013f2a7
-- statement:
--   Prove that \n $ (a + b + c + d)^4 + (a + b - c - d)^4 + (a - b + c - d)^4 + (a - b - c + d)^4 - (a + b + c - d)^4 - (a + b - c + d)^4 - (a - b + c + d)^4 - ( - a + b + c + d)^4 = 192abcd$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7988 {a b c d : ℤ} : (a + b + c + d)^4 + (a + b - c - d)^4 + (a - b + c - d)^4 + (a - b - c + d)^4 - (a + b + c - d)^4 - (a + b - c + d)^4 - (a - b + c + d)^4 - ( - a + b + c + d)^4 = 192 * a * b * c * d   :=  by sorry
