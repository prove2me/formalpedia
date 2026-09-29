-- Prove2me | Theorems.Thm_lean_workbook_plus_4427
-- name    : lean_workbook_plus_4427
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/ad7743b9-45c8-490f-8629-8264cfaa0f13
-- statement:
--   Let $a, b, c, d$ be real numbers with $a+d=b+c$ Prove that $(a-b)(c-d)+(a-c)(b-d)+(d-a)(b-c)\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4427 (a b c d : ℝ) (h : a + d = b + c) :
  (a - b) * (c - d) + (a - c) * (b - d) + (d - a) * (b - c) ≥ 0   :=  by sorry
