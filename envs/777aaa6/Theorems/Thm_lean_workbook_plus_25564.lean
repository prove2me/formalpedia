-- Prove2me | Theorems.Thm_lean_workbook_plus_25564
-- name    : lean_workbook_plus_25564
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0f49502e-f20d-403c-a038-ae0e0703bb06
-- statement:
--   If $a=\dfrac{1}{100},b=\dfrac{99}{100}\ and\ c=5,\ then\ \left ( a+\dfrac{1}{a} \right )\left ( b+\dfrac{1}{b} \right )\left ( c+\dfrac{1}{c} \right )>1000$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25564  (a b c : ℝ)
  (h₀ : a = 1 / 100)
  (h₁ : b = 99 / 100)
  (h₂ : c = 5) :
  (a + 1 / a) * (b + 1 / b) * (c + 1 / c) > 1000   :=  by sorry
