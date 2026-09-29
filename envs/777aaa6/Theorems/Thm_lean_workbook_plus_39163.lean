-- Prove2me | Theorems.Thm_lean_workbook_plus_39163
-- name    : lean_workbook_plus_39163
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/097d2c38-c06c-47a8-852c-72c9667b0ecb
-- statement:
--   Prove the Fibonacci identity $ F_{n+p+1}=F_{n+1}F_{p+1}+F_{n}F_{p}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39163 (n p : ℕ) : fib (n + p + 1) = fib (n + 1) * fib (p + 1) + fib n * fib p   :=  by sorry
