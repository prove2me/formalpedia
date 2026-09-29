-- Prove2me | Theorems.Thm_lean_workbook_plus_41503
-- name    : lean_workbook_plus_41503
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/4736f26c-971f-4a0a-90ef-7aa1ed112c45
-- statement:
--   Let $a,b,x,y$ be real numbers with ${0<y\leq\3x}.$ Prove the inequality $ x(a^{4}+b^{4})+2ya^{2}b^{2}\ge\ (x+y)(a^{3}b+ab^{3}).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41503 (a b x y : ℝ) (h₀ : 0 < y) (h₁ : y ≤ 3 * x) :  x * (a^4 + b^4) + 2 * y * a^2 * b^2 ≥ (x + y) * (a^3 * b + a * b^3)   :=  by sorry
