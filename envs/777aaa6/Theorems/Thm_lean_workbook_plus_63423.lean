-- Prove2me | Theorems.Thm_lean_workbook_plus_63423
-- name    : lean_workbook_plus_63423
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/924a6f91-0714-452d-a1d6-3cbca2ea6d96
-- statement:
--   For any odd number $ p$ , the numbers $ p^2-1$ and $ p^2+1$ are always even.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63423 (p : ℤ) (hp : p % 2 = 1) : (p^2 - 1) % 2 = 0 ∧ (p^2 + 1) % 2 = 0   :=  by sorry
