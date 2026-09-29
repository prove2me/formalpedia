-- Prove2me | Theorems.Thm_lean_workbook_plus_5966
-- name    : lean_workbook_plus_5966
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/dcd19bb3-ec80-407c-ba4c-a1be3534a8b2
-- statement:
--   Prove that $\frac{s^3+2}{3s}\geq 1$ given $s > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5966 (s : ℝ) (hs : s > 0) : (s^3 + 2) / (3 * s) ≥ 1   :=  by sorry
