-- Prove2me | Theorems.Thm_lean_workbook_plus_34462
-- name    : lean_workbook_plus_34462
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/768d27e3-841b-49a0-bc0f-be1f4abf0e2b
-- statement:
--   Prove that $ 3^k >= 1 + 2k$ for $ k > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34462 (k : ℕ) (h : k > 0) : (3 : ℝ)^k >= 1 + 2 * k   :=  by sorry
