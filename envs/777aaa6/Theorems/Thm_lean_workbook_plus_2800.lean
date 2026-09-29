-- Prove2me | Theorems.Thm_lean_workbook_plus_2800
-- name    : lean_workbook_plus_2800
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/c5ca6d8d-ccaf-4ac3-8fae-ce879c616169
-- statement:
--   Prove the inequality \(\frac{(a+b)(b+c)(c+a)}{8}\leq\frac{(a+b+c)^3}{27}\) where \(a, b, c > 1\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2800 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) : (a + b) * (b + c) * (c + a) / 8 ≤ (a + b + c) ^ 3 / 27   :=  by sorry
