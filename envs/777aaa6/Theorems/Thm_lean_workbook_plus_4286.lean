-- Prove2me | Theorems.Thm_lean_workbook_plus_4286
-- name    : lean_workbook_plus_4286
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/79d26118-b15b-4698-a9fb-0043c7087b21
-- statement:
--   Prove that $\frac{1}{\sqrt{k^2+k}}>\frac{1}{2k}$ for $k\geq1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4286 (k : ℕ) (h : 1 ≤ k) :
  (1:ℝ) / Real.sqrt (k ^ 2 + k) > (1:ℝ) / (2 * k)   :=  by sorry
