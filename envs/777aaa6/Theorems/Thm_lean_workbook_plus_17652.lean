-- Prove2me | Theorems.Thm_lean_workbook_plus_17652
-- name    : lean_workbook_plus_17652
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/4d762a0a-b122-490a-b9a9-e1a12a294a21
-- statement:
--   Your teacher graphed $|x| > \sqrt2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17652 (x : ℝ) : |x| > Real.sqrt 2 ↔ x < -Real.sqrt 2 ∨ x > Real.sqrt 2   :=  by sorry
