-- Prove2me | Theorems.Thm_lean_workbook_plus_75704
-- name    : lean_workbook_plus_75704
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/04ec1c1c-e915-4a80-990e-791b010f4485
-- statement:
--   Prove that\n\n $ (a+b)(a^2+b^2)(a^3+b^3) \le 4(a^6+b^6)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75704 (a b : ℝ) : (a+b)*(a^2+b^2)*(a^3+b^3) ≤ 4 * (a^6 + b^6)   :=  by sorry
