-- Prove2me | Theorems.Thm_lean_workbook_plus_71847
-- name    : lean_workbook_plus_71847
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/2d59d0d9-ea0c-4542-a2f5-24f229a66c44
-- statement:
--   Given that $a>0$ and $b>0$ prove that $\sqrt{ab}\ge\frac{2ab}{a+b}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71847 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Real.sqrt (a * b) ≥ 2 * a * b / (a + b)   :=  by sorry
