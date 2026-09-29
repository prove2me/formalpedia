-- Prove2me | Theorems.Thm_lean_workbook_plus_2438
-- name    : lean_workbook_plus_2438
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a4d57ff4-2931-4656-851c-5e9c6c85a754
-- statement:
--   Let $ a,b,c$ be positive real numbers. Prove that:\n $ a^{3}+b^{3}+c^{3}+ab^{2}+bc^{2}+ca^{2}\ge 2(a^{2}b+b^{2}c+c^{2}a)$\nAn easy one. I want to a non-SID-CID solution
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2438 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 + a * b^2 + b * c^2 + c * a^2 ≥ 2 * (a^2 * b + b^2 * c + c^2 * a)   :=  by sorry
