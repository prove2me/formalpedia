-- Prove2me | Theorems.Thm_lean_workbook_plus_7344
-- name    : lean_workbook_plus_7344
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/fc7d541d-f5ad-4d5c-a78d-5be45d5da19e
-- statement:
--   Suppose $f(n) = n-1$ for $n$ even, $f(n) = n+1$ for $n$ odd for $n \leq 2m, m\in \mathbb{Z}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7344 {m : ℤ} (f : ℤ → ℤ) (hf: f = fun n => if n % 2 = 0 then n-1 else n+1) : ∀ n ≤ 2*m, f n = if n % 2 = 0 then n-1 else n+1   :=  by sorry
