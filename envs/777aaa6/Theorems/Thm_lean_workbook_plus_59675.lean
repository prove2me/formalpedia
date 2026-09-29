-- Prove2me | Theorems.Thm_lean_workbook_plus_59675
-- name    : lean_workbook_plus_59675
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/faf7f5d0-b06e-4de6-81ed-4091ee408cad
-- statement:
--   Let $a,b,c>0$ .prove that $\sum_{cyc}\frac{ab}{a+b}\le\frac{3(ab+bc+ca)}{(2(a+b+c)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59675 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) ≤ (3 * (a * b + b * c + c * a)) / (2 * (a + b + c))   :=  by sorry
