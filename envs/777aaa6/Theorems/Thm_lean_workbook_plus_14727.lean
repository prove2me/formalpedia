-- Prove2me | Theorems.Thm_lean_workbook_plus_14727
-- name    : lean_workbook_plus_14727
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/45a68b7b-d633-49a5-8781-240f7ae1f0f6
-- statement:
--   $p=5$ $\implies$ Fibonacci sequence is $1,1,2,3,0,3,3,1,4, ...$ and so takes all residues values $0,1,2,3,4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14727 : ∀ n, ( fib n ≡ 0 [ZMOD 5] ∨ fib n ≡ 1 [ZMOD 5] ∨ fib n ≡ 2 [ZMOD 5] ∨ fib n ≡ 3 [ZMOD 5] ∨ fib n ≡ 4 [ZMOD 5])   :=  by sorry
