-- Prove2me | Theorems.Thm_lean_workbook_plus_70226
-- name    : lean_workbook_plus_70226
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/a354505b-5fca-4944-ab70-0ec534d371e2
-- statement:
--   Prove $\frac{3s}{2s+3}\leq\frac{s}{\sqrt{s+6}}$ for $s\geq 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70226 (s : ℝ) (hs : s ≥ 3) : (3 * s) / (2 * s + 3) ≤ s / Real.sqrt (s + 6)   :=  by sorry
