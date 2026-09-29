-- Prove2me | Theorems.Thm_lean_workbook_plus_52700
-- name    : lean_workbook_plus_52700
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/000eaf4a-f4cf-4f88-abe9-969636ce3987
-- statement:
--   If $ a > 1,n \ge 1$ ,then prove (a - 1) divides $a^n - 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52700 (a n : ℕ) (h₁ : a > 1) (h₂ : n ≥ 1) : a - 1 ∣ a ^ n - 1   :=  by sorry
