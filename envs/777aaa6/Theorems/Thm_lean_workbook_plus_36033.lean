-- Prove2me | Theorems.Thm_lean_workbook_plus_36033
-- name    : lean_workbook_plus_36033
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/254f8900-b9b1-4aa6-8300-ce9ad45e3610
-- statement:
--   Prove using polynomials that $(a+b+c)^5-a^5-b^5-c^5=5 (a+b)(b+c)(c+a)(a^2+b^2+c^2+ab+bc+ca) , \forall a,b,c \in \mathbb{C}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36033 {a b c : ℂ} : (a + b + c) ^ 5 - a ^ 5 - b ^ 5 - c ^ 5 = 5 * (a + b) * (b + c) * (c + a) * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a)   :=  by sorry
