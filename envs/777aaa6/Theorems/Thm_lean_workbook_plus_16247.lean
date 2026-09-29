-- Prove2me | Theorems.Thm_lean_workbook_plus_16247
-- name    : lean_workbook_plus_16247
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/5512a61d-61b9-4382-9599-bfba78a70af3
-- statement:
--   prove that : \n\n $ (x+1)(x^2+1)(x^3+1)\,\leq\,4(x^6+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16247 (x : ℝ) : (x + 1) * (x ^ 2 + 1) * (x ^ 3 + 1) ≤ 4 * (x ^ 6 + 1)   :=  by sorry
