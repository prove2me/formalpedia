-- Prove2me | Theorems.Thm_lean_workbook_plus_34548
-- name    : lean_workbook_plus_34548
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/3306db09-c9c8-42bd-8350-3cf09dd8a042
-- statement:
--   Prove that $\frac{1}{k^3}<\frac{1}{2}\left( \frac{1}{(k-1)^2}-\frac{1}{k^2} \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34548  (k : ℕ) (hk : 1 < k) :
  (1 : ℝ) / k^3 < 1 / 2 * (1 / (k - 1)^2 - 1 / k^2)   :=  by sorry
