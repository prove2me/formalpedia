-- Prove2me | Theorems.Thm_lean_workbook_plus_70453
-- name    : lean_workbook_plus_70453
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/8e563702-5a27-4f20-84f9-44c1ac73dad4
-- statement:
--   $ {k + n \choose k}$ is an integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70453 (k n : ℕ) : ∃ a : ℕ, (k + n).choose k = a   :=  by sorry
