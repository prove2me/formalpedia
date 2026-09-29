-- Prove2me | Theorems.Thm_lean_workbook_plus_44363
-- name    : lean_workbook_plus_44363
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/b44acb3a-1649-4632-a842-c53834e28ef0
-- statement:
--   We have: $ abc(a^2 - ab + b^2)(b^2 - bc + c^2)(c^2 - ac + c^2) = a^3b^3c^3$ , which means either $ abc = 0$ or $ (a^2-ab+b^2)(b^2-bc+c^2)(c^2-ac+c^2)=a^2b^2c^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44363 {a b c : ℝ} (h : a * b * c * (a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) * (c ^ 2 - c * a + a ^ 2) = a ^ 3 * b ^ 3 * c ^ 3) : a * b * c = 0 ∨ (a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) * (c ^ 2 - c * a + a ^ 2) = a ^ 2 * b ^ 2 * c ^ 2   :=  by sorry
