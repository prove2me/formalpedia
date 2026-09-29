-- Prove2me | Theorems.Thm_lean_workbook_plus_27603
-- name    : lean_workbook_plus_27603
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/be16d7b8-2b35-4be2-af59-5669af31a872
-- statement:
--   Given real numbers $a, b, c$ such that $a^2 +b^2 +c^2+(a+b+c)^2 \leq 4$ Prove that: $ \frac{ab+1}{(a+b)^2}+\frac{bc+1}{(b+c)^2}+\frac{ac+1}{(a+c)^2}\geq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27603 : ∀ a b c : ℝ, a^2 + b^2 + c^2 + (a + b + c)^2 ≤ 4 → (ab + 1) / (a + b)^2 + (bc + 1) / (b + c)^2 + (ac + 1) / (a + c)^2 ≥ 2   :=  by sorry
