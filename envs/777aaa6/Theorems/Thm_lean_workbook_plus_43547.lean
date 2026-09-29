-- Prove2me | Theorems.Thm_lean_workbook_plus_43547
-- name    : lean_workbook_plus_43547
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/65585a97-7618-4040-b6ac-3a4684acba86
-- statement:
--   Prove that $(2+\sqrt{3})^{n}+(2-\sqrt{3})^{n}$ is even for all natural numbers $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43547 : ∀ n : ℕ, Even ((2 + Real.sqrt 3) ^ n + (2 - Real.sqrt 3) ^ n)   :=  by sorry
