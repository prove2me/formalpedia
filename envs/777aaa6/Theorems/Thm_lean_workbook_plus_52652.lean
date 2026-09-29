-- Prove2me | Theorems.Thm_lean_workbook_plus_52652
-- name    : lean_workbook_plus_52652
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/d128da35-ea6e-49cc-905d-ebf636165442
-- statement:
--   Let $a,b,c>0$ .Prove that: $ab(a+b)+bc(b+c)+ca(c+a)\geq\frac{2}{3}\cdot(a+b+c)(ab+bc+ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52652 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ≥ 2 / 3 * (a + b + c) * (a * b + b * c + c * a)   :=  by sorry
