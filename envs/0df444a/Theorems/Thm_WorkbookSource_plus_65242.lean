-- Prove2me | Theorems.Thm_WorkbookSource_plus_65242
-- name    : WorkbookSource.plus_65242
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:44:33.685925+00:00
-- url     : https://prove2.me/theorems/24329d9e-287e-413b-8d7b-3d032cbb7092
-- title:
--   Representing every amount above three with two and five
-- statement:
--   Given debt N: If N is even and $N \ge 4$ , then use $\frac{N}{2}$ two dollar bills. If N is odd, use one 5 dollar bill and $\frac{N-5}{2}$ two dollar bills. This works for all $N \ge 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_65242` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_65242; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_65242 (N : ℕ) (hN : 4 ≤ N) : (N % 2 = 0 ∧ ∃ m:ℕ, N = 2*m) ∨ (N % 2 = 1 ∧ ∃ m:ℕ, N = 2*m + 5)   :=  by sorry
