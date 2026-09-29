-- Prove2me | Theorems.Thm_lean_workbook_plus_55189
-- name    : lean_workbook_plus_55189
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/71e60374-365a-443d-acf2-36c1d04cb78d
-- statement:
--   Prove that ${2}^n > {n}^2$ is true for all integers $n > 4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55189 : ∀ n : ℕ, n > 4 → 2^n > n^2   :=  by sorry
