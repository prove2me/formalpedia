-- Prove2me | Theorems.Thm_lean_workbook_plus_70549
-- name    : lean_workbook_plus_70549
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/749b6cec-4b12-4c46-a71a-e11a11831201
-- statement:
--   $a_n\geq a_{0}/2^n \leftrightarrow 2^na_n\geq a_0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70549 (a_0 a_n : ℝ) (n : ℕ) : a_n ≥ a_0 / (2^n) ↔ (2^n) * a_n ≥ a_0   :=  by sorry
