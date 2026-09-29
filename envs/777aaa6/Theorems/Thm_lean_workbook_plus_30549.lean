-- Prove2me | Theorems.Thm_lean_workbook_plus_30549
-- name    : lean_workbook_plus_30549
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/8badc64c-94e1-4d25-9617-7d5343b66515
-- statement:
--   $\sqrt{\frac{a}{a+b}}>\frac{a}{a+b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30549 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Real.sqrt (a / (a + b)) > a / (a + b)   :=  by sorry
