-- Prove2me | Theorems.Thm_lean_workbook_plus_18331
-- name    : lean_workbook_plus_18331
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/c9d21500-eb20-4239-b710-c9a958b07fbd
-- statement:
--   We have that $ 2(a^{2}+b^{2}+c^{2})(a+b+c)=3(ab+bc+ca)(a+b+c)$ or equivalently and then Schur\n $ 2(a^{3}+b^{3}+c^{3})=ab(a+b)+bc(b+c)+ca(c+a)+9abc\leq a^{3}+b^{3}+c^{3}+12abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18331  (a b c : ℝ) :
  2 * (a^2 + b^2 + c^2) * (a + b + c) = 3 * (a * b + b * c + c * a) * (a + b + c) ↔
  2 * (a^3 + b^3 + c^3) = a * b * (a + b) + b * c * (b + c) + c * a * (c + a) + 9 * a * b * c   :=  by sorry
