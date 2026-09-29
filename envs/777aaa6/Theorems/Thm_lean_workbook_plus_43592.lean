-- Prove2me | Theorems.Thm_lean_workbook_plus_43592
-- name    : lean_workbook_plus_43592
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/5b70d53b-c284-4793-ab0e-27c19965b36a
-- statement:
--   Prove that if $n \geq 2$, then $2^n - 1$ is congruent to 3 modulo 4.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43592 : ∀ n ≥ 2, (2^n - 1) % 4 = 3   :=  by sorry
