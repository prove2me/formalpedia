-- Prove2me | Theorems.Thm_lean_workbook_plus_55348
-- name    : lean_workbook_plus_55348
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/45e0655f-d464-4a70-8d87-9c920e2d031a
-- statement:
--   Prove that $\binom{n+1}{2}+\binom{n}{2}=n^{2}$ using combinatorial methods.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55348 (n : ℕ) : (n + 1).choose 2 + n.choose 2 = n^2   :=  by sorry
