-- Prove2me | Theorems.Thm_lean_workbook_plus_81533
-- name    : lean_workbook_plus_81533
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e3e6c90c-4ebd-4ff0-bc9e-83e16ec6a0d5
-- statement:
--   $\frac{\sqrt{a+b}}{\sqrt{2}}\geq\frac{2}{\frac{1}{\sqrt{a}}+\frac{1}{\sqrt{b}}}\Longleftrightarrow\sqrt{a+b}(\frac{1}{\sqrt{a}}+\frac{1}{\sqrt{b}})\geq2\sqrt{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81533 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (Real.sqrt (a + b) / Real.sqrt 2) ≥ 2 / (1 / Real.sqrt a + 1 / Real.sqrt b) ↔ Real.sqrt (a + b) * (1 / Real.sqrt a + 1 / Real.sqrt b) ≥ 2 * Real.sqrt 2   :=  by sorry
