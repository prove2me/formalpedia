-- Prove2me | Theorems.Thm_lean_workbook_plus_6935
-- name    : lean_workbook_plus_6935
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3366aad8-4e0c-4225-bf40-34a7d05543ef
-- statement:
--   Prove that $(a+b)(b+c)+(b+c)(c+a)+(c+a)(a+b)=a^2+b^2+c^2+3(ab+bc+ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6935 : (a + b) * (b + c) + (b + c) * (c + a) + (c + a) * (a + b) = a ^ 2 + b ^ 2 + c ^ 2 + 3 * (a * b + b * c + c * a)   :=  by sorry
