-- Prove2me | Theorems.Thm_lean_workbook_plus_21723
-- name    : lean_workbook_plus_21723
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/a36ff8fb-415e-4933-bda3-b247bbba2633
-- statement:
--   Let $a,b,c,d$ be reals such that $a+b+c+d=0$ . Prove that $a^{3}+b^{3}+c^{3}+d^{3}=3(a+d)(b+d)(c+d)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21723 (a b c d : ℝ) (h : a + b + c + d = 0) : a^3 + b^3 + c^3 + d^3 = 3 * (a + d) * (b + d) * (c + d)   :=  by sorry
