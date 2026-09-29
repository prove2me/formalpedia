-- Prove2me | Theorems.Thm_lean_workbook_plus_29636
-- name    : lean_workbook_plus_29636
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f4998590-99e8-44f9-b5c5-23b5cb79dd1d
-- statement:
--   Prove that there exist infinitely positive integers $n$ that $a+b+c | a^n+b^n+c^n$ where $a+b+c | a^2+b^2+c^2$ . You should add this ' $a + b + c \neq 0$ '
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29636 (a b c : ℤ) (h : a + b + c ≠ 0) (habc : a + b + c ∣ a^2 + b^2 + c^2) : ∃ n : ℕ, a + b + c ∣ a^n + b^n + c^n   :=  by sorry
