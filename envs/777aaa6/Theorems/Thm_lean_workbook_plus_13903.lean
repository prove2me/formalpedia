-- Prove2me | Theorems.Thm_lean_workbook_plus_13903
-- name    : lean_workbook_plus_13903
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/cbd21a94-e6d8-4416-a2cb-bd70b6cc52b4
-- statement:
--   Prove that $\frac{2x}{2x+1} > \sqrt{\frac{2x-1}{2x+1}}$ for all positive $x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13903 (x : ℝ) (hx : 0 < x) : (2*x) / (2*x + 1) > Real.sqrt ((2*x - 1) / (2*x + 1))   :=  by sorry
