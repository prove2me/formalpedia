-- Prove2me | Theorems.Thm_lean_workbook_plus_75408
-- name    : lean_workbook_plus_75408
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/4d9edd4e-7cf5-45fc-96bd-aa2d0c6e45ca
-- statement:
--   Let $a, b$ , and $c$ be integers such that $a+b+c$ divides $a^2 +b^2 +c^2$ . Prove that there are infinitely many positive integers $n$ such that $a+b+c$ divides $a^n +b^n +c^n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75408 (a b c : ℤ) (h : a+b+c ∣ a^2 + b^2 + c^2) : ∃ n : ℕ, a+b+c ∣ a^n + b^n + c^n   :=  by sorry
