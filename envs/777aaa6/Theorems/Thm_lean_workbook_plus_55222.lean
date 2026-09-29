-- Prove2me | Theorems.Thm_lean_workbook_plus_55222
-- name    : lean_workbook_plus_55222
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/1cfdcaaf-f2c1-419c-acdb-83ccbbf1765d
-- statement:
--   Prove $\forall a,b,c \in \mathbb{R^+}$ : $4(a+b+c)^3 > 27(a^3+b^3+c^3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55222 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 4 * (a + b + c) ^ 3  > 27 * (a ^ 3 + b ^ 3 + c ^ 3)   :=  by sorry
