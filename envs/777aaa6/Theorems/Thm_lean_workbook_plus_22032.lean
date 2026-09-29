-- Prove2me | Theorems.Thm_lean_workbook_plus_22032
-- name    : lean_workbook_plus_22032
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/7532278f-32db-477b-ada6-56c290c52754
-- statement:
--   (S2 : $(P(x),Q(x))=(cx,cx+d)\quad\forall x)$ whatever are $c,d\in\mathbb R$ , $c\ne 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22032 (c d : ℝ) (hc : c ≠ 0) (P Q : ℝ → ℝ) (hPQ: ∀ x, (P x, Q x) = (c * x, c * x + d)) : ∃ c' d', c' ≠ 0 ∧ ∀ x, (P x, Q x) = (c' * x, c' * x + d')   :=  by sorry
