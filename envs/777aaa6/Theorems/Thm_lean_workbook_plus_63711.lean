-- Prove2me | Theorems.Thm_lean_workbook_plus_63711
-- name    : lean_workbook_plus_63711
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/7ee0931e-94b8-4b27-b7f4-31e582ac5dfb
-- statement:
--   Prove that $1\cdot 4 + 2\cdot 5 + 3\cdot 6 + \cdots + n(n+3) = \frac{n(n+1)(n+5)}{3}$ for all positive integer $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63711 (n : ℕ) : ∑ k in Finset.range (n+1), (k * (k + 3)) = n * (n + 1) * (n + 5) / 3   :=  by sorry
