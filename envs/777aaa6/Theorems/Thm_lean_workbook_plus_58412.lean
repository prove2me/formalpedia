-- Prove2me | Theorems.Thm_lean_workbook_plus_58412
-- name    : lean_workbook_plus_58412
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/19acffc6-25b3-490d-9643-0f43f023156b
-- statement:
--   If $a+b+c\ge 3\Rightarrow \frac{6}{a+b+c-1} \le 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58412 (a b c : ℝ) (h : a + b + c ≥ 3) : 6 / (a + b + c - 1) ≤ 3   :=  by sorry
