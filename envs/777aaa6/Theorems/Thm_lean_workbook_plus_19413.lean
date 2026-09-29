-- Prove2me | Theorems.Thm_lean_workbook_plus_19413
-- name    : lean_workbook_plus_19413
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/cac53af9-9f7a-4e27-a803-e7148350f52a
-- statement:
--   If $ a,b,c>0 $ prove that: \n $ (a+b+c)(\\frac{1}{a}+\\frac{1}{b}+\\frac{1}{c}\\ge\\frac{3(a+b+c)^2}{ab+bc+ca} $ \n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19413 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 3 * (a + b + c) ^ 2 / (a * b + b * c + a * c)   :=  by sorry
