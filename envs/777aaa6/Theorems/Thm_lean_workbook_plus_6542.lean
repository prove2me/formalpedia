-- Prove2me | Theorems.Thm_lean_workbook_plus_6542
-- name    : lean_workbook_plus_6542
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/7c284b70-2758-4fba-974c-afa6b52bd826
-- statement:
--   Let $ a,b,c>0$ . Prove that \n\n $ (a+b+c)(a^2+b^2+c^2) \le \frac{1}{9} (a+b+c)^3 +2(a^3+b^3+c^3)$\n\n<=> \n\n $ 0\leq \left( 5\,a+5\,b-c \right) \left( a-b \right) ^{2}+ \left( 5\,b+5\,c-a \right) \left( b-c \right) ^{2}+ \left( 5\,c+5\,a-b \right) \left( c-a \right) ^{2},$ \n\nso that,easy. \nBQ
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6542 (a b c : ℝ) : (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 1 / 9 * (a + b + c) ^ 3 + 2 * (a ^ 3 + b ^ 3 + c ^ 3) ↔ 0 ≤ (5 * a + 5 * b - c) * (a - b) ^ 2 + (5 * b + 5 * c - a) * (b - c) ^ 2 + (5 * c + 5 * a - b) * (c - a) ^ 2   :=  by sorry
