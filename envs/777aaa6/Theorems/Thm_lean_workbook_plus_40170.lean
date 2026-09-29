-- Prove2me | Theorems.Thm_lean_workbook_plus_40170
-- name    : lean_workbook_plus_40170
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/6350c405-408c-4f47-a16d-577567017609
-- statement:
--   Prove that $(2- \sqrt{3})^{n} + (2+ \sqrt{3})^{n}$ is an even number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40170 : ∀ n : ℕ, Even ((2 - Real.sqrt 3)^n + (2 + Real.sqrt 3)^n)   :=  by sorry
