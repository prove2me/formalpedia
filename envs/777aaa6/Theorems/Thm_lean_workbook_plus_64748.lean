-- Prove2me | Theorems.Thm_lean_workbook_plus_64748
-- name    : lean_workbook_plus_64748
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/cc4b9151-7357-4345-a577-81a992069722
-- statement:
--   Prove that if $f(x)$ is a polynomial with all integer coefficients, and two numbers $a$ and $b$ are the same modulo $c$, then $f(a)$ and $f(b)$ are also the same modulo $c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64748 {f : Polynomial ℤ} {a b c : ℤ} (h₁ : a ≡ b [ZMOD c]) : f.eval a ≡ f.eval b [ZMOD c]   :=  by sorry
