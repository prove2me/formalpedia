-- Prove2me | Theorems.Thm_lean_workbook_plus_66696
-- name    : lean_workbook_plus_66696
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/d0fb8544-56a6-4873-ba1c-041f7275a7fa
-- statement:
--   If $P$ is a polynomial with integer coefficients, then $a-b | P(a)-P(b)$ for any integers $a\neq b.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66696 (P : Polynomial ℤ) (a b : ℤ) (h : a ≠ b) : a - b ∣ P.eval a - P.eval b   :=  by sorry
