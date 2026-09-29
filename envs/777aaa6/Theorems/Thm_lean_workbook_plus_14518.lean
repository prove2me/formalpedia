-- Prove2me | Theorems.Thm_lean_workbook_plus_14518
-- name    : lean_workbook_plus_14518
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/7a0a46c2-95ae-496c-9a3e-dab0dc68017c
-- statement:
--   Let $a,b,c,d$ are real numbers such that $a+b+c+d=4$ and $ab+cd=8$ . Prove that\n\n $$ a^2+b^2+c^2+d^2\geq16$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14518 (a b c d : ℝ) (h1 : a + b + c + d = 4) (h2 : a * b + c * d = 8) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 16   :=  by sorry
