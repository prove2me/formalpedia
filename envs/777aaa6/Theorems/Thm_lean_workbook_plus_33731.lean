-- Prove2me | Theorems.Thm_lean_workbook_plus_33731
-- name    : lean_workbook_plus_33731
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/3cbfffb2-163c-4709-866f-bf7f8b0ee8fb
-- statement:
--   We have: $x^3 \geq x$ for integer $x$ such that $-1\le x \le2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33731 :
  ∀ x : ℤ, -1 ≤ x ∧ x ≤ 2 → x^3 ≥ x   :=  by sorry
