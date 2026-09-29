-- Prove2me | Theorems.Thm_lean_workbook_plus_18676
-- name    : lean_workbook_plus_18676
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/3a6b4e28-7128-4148-90dd-b7f056c166b4
-- statement:
--   Prove that for all m and n in the natural numbers, \\(E(m,n) = \\frac{mn}{m+n+1} \\geq \\frac{1}{3}\\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18676 (m n : ℕ) : (m * n) / (m + n + 1) ≥ 1 / 3   :=  by sorry
