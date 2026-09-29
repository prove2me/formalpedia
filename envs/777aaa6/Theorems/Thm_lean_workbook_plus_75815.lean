-- Prove2me | Theorems.Thm_lean_workbook_plus_75815
-- name    : lean_workbook_plus_75815
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d777a8fe-54df-4bcf-960f-72e3a8f4a13b
-- statement:
--   Prove that the cyclic sum $\sum_{cyc}(2a-b-c)sin\frac{A}{2}$ is equal to $\sum_{cyc}(a-b)(\sin \frac{A}{2}-\sin \frac{B}{2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75815 (a b c A : ℝ) : (2 * a - b - c) * Real.sin (A / 2) + (2 * b - c - a) * Real.sin (B / 2) + (2 * c - a - b) * Real.sin (C / 2) = (a - b) * (Real.sin (A / 2) - Real.sin (B / 2)) + (b - c) * (Real.sin (B / 2) - Real.sin (C / 2)) + (c - a) * (Real.sin (C / 2) - Real.sin (A / 2))   :=  by sorry
