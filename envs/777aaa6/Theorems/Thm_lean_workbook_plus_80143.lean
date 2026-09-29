-- Prove2me | Theorems.Thm_lean_workbook_plus_80143
-- name    : lean_workbook_plus_80143
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/95a86d76-7462-4782-9aed-329cfe9e285c
-- statement:
--   From the polynomial $x^2 + qx+p = (x-a)(x-b)$ , we have $q = -(a+b)$ and $p = ab$ for some integers $a, \; b$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80143 {p q a b : ℤ} (h₁ : p = a * b) (h₂ : q = -(a + b)) : p + q * x + x ^ 2 = (x - a) * (x - b)   :=  by sorry
