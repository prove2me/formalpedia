-- Prove2me | Theorems.Thm_lean_workbook_plus_67233
-- name    : lean_workbook_plus_67233
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/0d02768d-da22-44dd-83f0-4bbf10a28d5c
-- statement:
--   Note that $a(a+1)(a+2)(a+3)=(a^2+3a+1)^2-1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67233 : ∀ a : ℤ, a * (a + 1) * (a + 2) * (a + 3) = (a ^ 2 + 3 * a + 1) ^ 2 - 1   :=  by sorry
