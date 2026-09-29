-- Prove2me | Theorems.Thm_lean_workbook_plus_68934
-- name    : lean_workbook_plus_68934
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/bc2ca440-f71e-4ac4-9199-dde68effe544
-- statement:
--   Prove that $\binom{n+1}{2}=\frac{n(n+1)}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68934 (n : ℕ) : (n + 1).choose 2 = n * (n + 1) / 2   :=  by sorry
