-- Prove2me | Theorems.Thm_WorkbookSource_problem_5769
-- name    : WorkbookSource.problem_5769
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:50.686737+00:00
-- url     : https://prove2.me/theorems/b52c4b00-0b67-4b13-9f4d-e284e3df0711
-- title:
--   An incompatible sum and pair-product system
-- statement:
--   Let $ a,b,c$ be real numbers and $ n,k$ be positive real numbers. Suppose that we have
--
--   $a+b+c=n$
--   $ab+bc+ca=k$
--
--   Prove that there are no real $ a,b,c$ that satisfy the equations if $ k\geq\frac{n^{2}}{2}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5769` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5769; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_5769 (n k : ℝ) (hn : n > 0) (hk : k ≥ (n^2)/2) : ¬∃ a b c : ℝ, a + b + c = n ∧ a * b + b * c + c * a = k  :=  by sorry
