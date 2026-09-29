-- Prove2me | Theorems.Thm_lean_workbook_plus_29968
-- name    : lean_workbook_plus_29968
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/a56c7ba2-fb4a-494d-b26e-410d1efed9fa
-- statement:
--   Prove that $(3+\sqrt{5})^n+(3-\sqrt{5})^n$ is an even integer for all natural numbers $n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29968 (n : ℕ) : Even ((3 + Real.sqrt 5) ^ n + (3 - Real.sqrt 5) ^ n)   :=  by sorry
