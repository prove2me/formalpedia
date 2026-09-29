-- Prove2me | Theorems.Thm_lean_workbook_plus_30951
-- name    : lean_workbook_plus_30951
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/186dd45c-c973-4e85-bd3f-4d47aa9ccec0
-- statement:
--   If $gcd(a,b)=1$ then prove that $gcd(a^2+b^2,a^2b^2)=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30951 (a b : ℕ) (hab : Nat.Coprime a b) : Nat.Coprime (a^2 + b^2) (a^2 * b^2)   :=  by sorry
