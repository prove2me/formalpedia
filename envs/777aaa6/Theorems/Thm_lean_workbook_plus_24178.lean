-- Prove2me | Theorems.Thm_lean_workbook_plus_24178
-- name    : lean_workbook_plus_24178
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/2de2a621-87a5-47b6-8136-2fe277345a64
-- statement:
--   Prove that $1 \leq \phi(n) \leq n-1$ with all $n \geq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24178 (n : ℕ) (hn : 2 ≤ n) : 1 ≤ φ n ∧ φ n ≤ n - 1   :=  by sorry
