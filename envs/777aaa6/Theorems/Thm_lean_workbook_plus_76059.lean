-- Prove2me | Theorems.Thm_lean_workbook_plus_76059
-- name    : lean_workbook_plus_76059
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/c4969034-6e6e-4849-b054-5dde6cc9c1e1
-- statement:
--   Show that the range of $ f(x) = b^x $ for $ b > 1$ is $ (0, \infty)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76059 (b : ℝ) (hb : 1 < b) : Set.range (λ x : ℝ => b^x) = Set.Ioi 0   :=  by sorry
