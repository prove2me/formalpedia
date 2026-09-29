-- Prove2me | Theorems.Thm_lean_workbook_plus_64511
-- name    : lean_workbook_plus_64511
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/ec99279e-fb9b-408d-8ee7-e08b083c8f8a
-- statement:
--   Let $a,$ $b$ and $c$ are positive real numbers, such that $abc=1.$ Prove that $a^2+b^2+c^2+ab+ac+bc+6\geq4(a+b+c).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64511 (a b c : ℝ) (h : a * b * c = 1) :
  a^2 + b^2 + c^2 + a * b + b * c + a * c + 6 ≥ 4 * (a + b + c)   :=  by sorry
