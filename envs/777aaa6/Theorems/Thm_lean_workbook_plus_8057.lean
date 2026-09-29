-- Prove2me | Theorems.Thm_lean_workbook_plus_8057
-- name    : lean_workbook_plus_8057
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/258ee93c-b5eb-42e5-8c2a-df89175a4885
-- statement:
--   prove $2\,ab+2\,bc+2\,ac\geq {\frac { \left( b+c-a \right) \left( a+b \right) \left( c+a \right) }{b+c}}+{\frac { \left( a+c-b \right) \left( b+c \right) \left( a+b \right) }{c+a}}+{\frac { \left( a+b-c \right) \left( c+a \right) \left( b+c \right) }{a+b}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8057 : ∀ a b c : ℝ, 2 * a * b + 2 * b * c + 2 * a * c ≥ (b + c - a) * (a + b) * (c + a) / (b + c) + (a + c - b) * (b + c) * (a + b) / (c + a) + (a + b - c) * (c + a) * (b + c) / (a + b)   :=  by sorry
