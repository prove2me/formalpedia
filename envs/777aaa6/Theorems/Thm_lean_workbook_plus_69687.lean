-- Prove2me | Theorems.Thm_lean_workbook_plus_69687
-- name    : lean_workbook_plus_69687
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/ce93e4cb-0205-4dd0-b21d-cc6c2cbd9891
-- statement:
--   prove \( \cos a+\cos b=2\cdot \cos \frac{a+b}{2}\cdot \cos \frac{a-b}{2} \)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69687 (a b : ℝ) : Real.cos a + Real.cos b = 2 * Real.cos ((a + b) / 2) * Real.cos ((a - b) / 2)   :=  by sorry
