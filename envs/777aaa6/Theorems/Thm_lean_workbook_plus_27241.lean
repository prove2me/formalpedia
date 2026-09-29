-- Prove2me | Theorems.Thm_lean_workbook_plus_27241
-- name    : lean_workbook_plus_27241
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/ad6a301f-98b8-4f29-a39d-b8ebd160330d
-- statement:
--   If $n = 2k+1$ then $n = k + (k+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27241 (n k : ℕ) (h₁ : n = 2 * k + 1) : n = k + (k + 1)   :=  by sorry
