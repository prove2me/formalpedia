-- Prove2me | Theorems.Thm_lean_workbook_plus_32528
-- name    : lean_workbook_plus_32528
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/b6882611-f4b9-4754-826a-ece50ce6a601
-- statement:
--   Prove the inequality: $ \sqrt{\frac{a^2+b^2}{2}} \ge \dfrac{a+b}{2} $ for positive numbers $a, b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32528 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :  Real.sqrt ((a^2 + b^2) / 2) ≥ (a + b) / 2   :=  by sorry
