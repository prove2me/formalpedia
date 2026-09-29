-- Prove2me | Theorems.Thm_WorkbookSource_problem_42477
-- name    : WorkbookSource.problem_42477
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:37:09.385241+00:00
-- url     : https://prove2.me/theorems/ab0510cb-d6fe-41be-9343-d70d35a6f8e3
-- title:
--   Evaluating a multiplicative sequence at2007
-- statement:
--   Let numerical sequence $(u_{n})$, $n\in \mathbb{N}$ such that:
--   1. $(\forall n, m \in \mathbb{N}): u_{mn} = u_{m}.u_{n}$
--   2. $u_{10} = 0$
--   3. $u(k) = 0$ if $k \equiv 3 \mod 10$. Compute $u_{2007}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_42477` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_42477; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_42477 (u : ℕ → ℕ) (h1 : ∀ m n : ℕ, u (m * n) = u m * u n) (h2 : u 10 = 0) (h3 : ∀ k : ℕ, k % 10 = 3 → u k = 0) : u 2007 = 0  :=  by sorry
