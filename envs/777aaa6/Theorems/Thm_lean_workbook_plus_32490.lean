-- Prove2me | Theorems.Thm_lean_workbook_plus_32490
-- name    : lean_workbook_plus_32490
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/0e867114-d11a-4cab-990c-62e1e0a890aa
-- statement:
--   Find a root of the polynomial $f(X) = X^{4}+X+1$ over $\mathbb F_{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32490 : ∃ x : ℤ, x^4 + x + 1 ≡ 0 [ZMOD 2]   :=  by sorry
