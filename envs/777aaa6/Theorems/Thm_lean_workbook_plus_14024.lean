-- Prove2me | Theorems.Thm_lean_workbook_plus_14024
-- name    : lean_workbook_plus_14024
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/2d4b1b93-7265-4b91-9531-2e0c818b7fc6
-- statement:
--   $ 3$ divides $ x$ , so $ x=3a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14024 (x : ℤ) (h : 3 ∣ x) : ∃ a : ℤ, x = 3 * a   :=  by sorry
