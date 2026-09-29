-- Prove2me | Theorems.Thm_lean_workbook_plus_22881
-- name    : lean_workbook_plus_22881
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/e944c7e7-7d8e-43c5-91aa-f26f175b836d
-- statement:
--   Prove: $9a^{10}\geq 8a+1$ if $a \geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22881 (a : ℝ) (h : a ≥ 1) : 9 * a ^ 10 ≥ 8 * a + 1   :=  by sorry
