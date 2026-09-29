-- Prove2me | Theorems.Thm_lean_workbook_plus_6326
-- name    : lean_workbook_plus_6326
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/180b1f8c-4ade-4d9b-9380-ff64fa4478ec
-- statement:
--   If $x$ is a perfect square, then what is $4x$ ? And $9x$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6326 (x : ℕ) (hx : ∃ k, k^2 = x) : ∃ k, k^2 = 4*x ∧ ∃ k, k^2 = 9*x   :=  by sorry
