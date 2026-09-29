-- Prove2me | Theorems.Thm_lean_workbook_plus_47129
-- name    : lean_workbook_plus_47129
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/b46ec1d3-8c4b-4339-86a2-9e78af42e90c
-- statement:
--   From the condition we have $(a+b+c)(a^2+b^2+c^2-ab-bc-ca)=1$ . Therefore $a^2+b^2+c^2= \frac{1}{a+b+c}+ab+bc+ca$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47129  (a b c : ℂ)
  (h₀ : (a + b + c) * (a^2 + b^2 + c^2 - a * b - b * c - c * a) = 1) :
  a^2 + b^2 + c^2 = 1 / (a + b + c) + a * b + b * c + c * a   :=  by sorry
