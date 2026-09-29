-- Prove2me | Theorems.Thm_lean_workbook_plus_890
-- name    : lean_workbook_plus_890
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/eb35d6b0-610e-40e6-a20c-aa2fc9ed063b
-- statement:
--   Prove that $9^{n-1} + 3^{n-1} + 1$ is odd for all positive integers $n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_890 : ∀ n : ℕ, Odd (9^(n-1) + 3^(n-1) + 1)   :=  by sorry
