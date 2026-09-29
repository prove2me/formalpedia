-- Prove2me | Theorems.Thm_WorkbookSource_plus_6014
-- name    : WorkbookSource.plus_6014
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:41:22.432054+00:00
-- url     : https://prove2.me/theorems/efb7966e-c08c-4409-9a3a-e1fd2c588d1e
-- title:
--   A linear combination of two sequence limits
-- statement:
--   If $\lim_{n \to \infty}(3a_{n}+4b_{n}) = 8$ , $\lim_{n \to \infty}(6a_{n}-b_{n}) = 1$ , find $\lim_{n \to \infty}(2a_{n}-5b_{n})$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_6014` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_6014; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_6014 (a b : ℕ → ℝ) (h₁ : ∀ ε > 0, ∃ N, ∀ n ≥ N, |(3 * a n + 4 * b n) - 8| < ε) (h₂ : ∀ ε > 0, ∃ N, ∀ n ≥ N, |(6 * a n - b n) - 1| < ε) : ∀ ε > 0, ∃ N, ∀ n ≥ N, |(2 * a n - 5 * b n) - (-67 / 9)| < ε   :=  by sorry
