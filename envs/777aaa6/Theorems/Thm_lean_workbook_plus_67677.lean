-- Prove2me | Theorems.Thm_lean_workbook_plus_67677
-- name    : lean_workbook_plus_67677
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/4d181b4a-390c-41bc-8c69-ef571c75e23b
-- statement:
--   Find a solution for $(x,y,z)$ in the form $(5^n*2^{n-1}, 10^n, 5^{2n} *2^{2n-1})$ where $n$ is a natural number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67677 (x y z : ℕ) (n : ℕ) (hn: x = 5^n*2^(n-1) ∧ y = 10^n ∧ z = 5^(2*n)*2^(2*n-1)) : x*y*z = 10^n * (5^n * 2^(n-1)) * (5^(2*n) * 2^(2*n-1))   :=  by sorry
