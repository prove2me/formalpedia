-- Prove2me | Theorems.Thm_lean_workbook_plus_27614
-- name    : lean_workbook_plus_27614
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/8ed2bd76-0122-451b-a3ed-b89ab03458f5
-- statement:
--   Find $d_{20}$ where $a_{n}=b_{n-1}$, $b_{n}=a_{n-1}+c_{n-1}$, $c_{n}=a_{n-1}+b_{n-1}$, $d_n=a_n+b_n+c_n$, $a_1=2$, $b_1=2$, $c_1=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27614 (a b c d : ℕ → ℕ) (h₁ : a 1 = 2) (h₂ : b 1 = 2) (h₃ : c 1 = 1) (h₄ : ∀ n, a (n + 1) = b n) (h₅ : ∀ n, b (n + 1) = a n + c n) (h₆ : ∀ n, c (n + 1) = a n + b n) (h₇ : ∀ n, d n = a n + b n + c n) : d 20 = 20   :=  by sorry
