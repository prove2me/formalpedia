-- Prove2me | Theorems.Thm_lean_workbook_plus_11632
-- name    : lean_workbook_plus_11632
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/addb71ea-6b6e-4304-9d8e-763886d610d5
-- statement:
--   Prove that $\binom{n+1}{2}=\frac{n(n+1)}{2}$ for all integers $n\ge2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11632 (n : ℕ) (h : n ≥ 2) : (n + 1).choose 2 = n * (n + 1) / 2   :=  by sorry
