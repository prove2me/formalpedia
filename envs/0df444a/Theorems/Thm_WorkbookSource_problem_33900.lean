-- Prove2me | Theorems.Thm_WorkbookSource_problem_33900
-- name    : WorkbookSource.problem_33900
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:37:25.971667+00:00
-- url     : https://prove2.me/theorems/96096943-f33c-465d-a341-a6c376b5f8cd
-- title:
--   The eighth term of a pair of rational recurrences
-- statement:
--   Define two sequences of rational numbers as follows: let $a_0 = 2$ and $b_0 = 3$ , and recursively define $a_n = \frac{a_{n-1}^2}{b_{n-1}}$ and $b_n=\frac{b_{n-1}^2}{a_{n-1}}$ . Find $b_8$ , leaving your answer in the exponential form $m^n/p^q$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33900` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33900; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_33900 (b : ℕ → ℚ) (a : ℕ → ℚ) (b0 : b 0 = 3) (a0 : a 0 = 2) (hb : ∀ n, b (n + 1) = (b n)^2 / a n) (ha : ∀ n, a (n + 1) = (a n)^2 / b n) : b 8 = (3^3281)/2^3280  :=  by sorry
