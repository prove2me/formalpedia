-- Prove2me | Theorems.Thm_lean_workbook_plus_39698
-- name    : lean_workbook_plus_39698
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/17fdc1fb-54a6-48e0-b708-7c4e9667be02
-- statement:
--   Let $a,b,c,d\geq 0$ ,prove that: \n\n ${\frac {{a}^{3}}{ \left( b+c \right) \left( c+d \right) \left( b+d \right) }}+{\frac {{b}^{3}}{ \left( c+d \right) \left( d+a \right) \left( c+a \right) }}+{\frac {{c}^{3}}{ \left( d+a \right) \left( a+b \right) \left( b+d \right) }}+{\frac {{d}^{3}}{ \left( a+b \right) \left( b+c \right) \left( c+a \right) }}\geq \frac{1}{2}$ \n\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39698 : ∀ a b c d : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 → a^3 / (b + c) / (c + d) / (b + d) + b^3 / (c + d) / (d + a) / (c + a) + c^3 / (d + a) / (a + b) / (b + d) + d^3 / (a + b) / (b + c) / (c + a) ≥ 1 / 2   :=  by sorry
