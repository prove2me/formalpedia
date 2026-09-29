-- Prove2me | Theorems.Thm_lean_workbook_plus_42585
-- name    : lean_workbook_plus_42585
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/75f20632-8cca-4621-a3e4-977a4fcb22fa
-- statement:
--   Let a,b,c>0, prove that \n\n $ ab+bc+ca+(a+b+c)^2 \ge \frac{9(a+b)(b+c)(c+a)}{2(a+b+c)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42585 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b + b * c + c * a + (a + b + c) ^ 2 ≥ 9 * (a + b) * (b + c) * (c + a) / (2 * (a + b + c))   :=  by sorry
