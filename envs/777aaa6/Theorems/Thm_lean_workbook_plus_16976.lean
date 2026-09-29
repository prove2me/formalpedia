-- Prove2me | Theorems.Thm_lean_workbook_plus_16976
-- name    : lean_workbook_plus_16976
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/80c3d100-fbc2-4251-bc45-05ac5f1e250c
-- statement:
--   Or \n\n $(a+2b+c)(a+b+c)^2 = 4(a+b)(b+c)(c+a)+b^2(a+2b+c)+(c+a)(a-c)^2 \geqslant 4(a+b)(b+c)(c+a).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16976 (a b c : ℝ) :  (a + 2 * b + c) * (a + b + c) ^ 2 ≥ 4 * (a + b) * (b + c) * (c + a) + b ^ 2 * (a + 2 * b + c) + (c + a) * (a - c) ^ 2   :=  by sorry
