-- Prove2me | Theorems.Thm_lean_workbook_plus_78905
-- name    : lean_workbook_plus_78905
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/691d2c10-a7ee-4083-9291-a871ebc83390
-- statement:
--   Factorization: $x^2-y^2=(x+y)(x-y)$ $x^3-y^3=(x-y)(x^2+xy+y^2)$ $x^3+y^3=(x+y)(x^2-xy+y^2)$ Then can anyone tell me what is $x^4+y^4$ And $x^5-y^5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78905 (x y : ℤ) : x^2 - y^2 = (x + y) * (x - y) ∧ x^3 - y^3 = (x - y) * (x^2 + x * y + y^2) ∧ x^3 + y^3 = (x + y) * (x^2 - x * y + y^2)   :=  by sorry
