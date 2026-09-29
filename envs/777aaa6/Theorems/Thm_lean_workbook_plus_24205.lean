-- Prove2me | Theorems.Thm_lean_workbook_plus_24205
-- name    : lean_workbook_plus_24205
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/748b9e26-32c1-4c36-b0b5-7950f7a477b0
-- statement:
--   Prove that $n(n+1)(2n+1)/6 \leq 2003$ implies $n \leq 17$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24205 (n : ℕ) : (n * (n + 1) * (2 * n + 1) / 6) ≤ 2003 → n ≤ 17   :=  by sorry
