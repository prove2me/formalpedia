-- Prove2me | Theorems.Thm_lean_workbook_plus_43955
-- name    : lean_workbook_plus_43955
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/7bb23e4f-e062-4ab5-b3cd-c568829e4d44
-- statement:
--   The percent increase of a population is $\frac{Final Population-Initial Population}{Initial Population}*100$ %
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43955 (final initial : ℕ) : (final - initial)/initial * 100 = ((final:ℝ) - (initial:ℝ)) / (initial:ℝ) * 100   :=  by sorry
