-- Prove2me | Theorems.Thm_lean_workbook_plus_65861
-- name    : lean_workbook_plus_65861
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/763c5600-a101-4ae0-8329-962e7603244b
-- statement:
--   Does $\lfloor a \rfloor =b$ imply $a-1 \le b \le a$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65861 (a b : ℝ) (h : ⌊a⌋ = b) : a - 1 ≤ b ∧ b ≤ a   :=  by sorry
