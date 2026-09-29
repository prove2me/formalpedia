-- Prove2me | Theorems.Thm_lean_workbook_plus_32212
-- name    : lean_workbook_plus_32212
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/d3f1ad44-4eca-438a-80dc-9abdf6f491c2
-- statement:
--   The only constant solution is $\boxed{\text{S1 : }f(x)=0\text{ }\forall x\in\mathbb Z}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32212 (f : ℤ → ℤ) (h : ∃ c, ∀ x, f x = c) : ∃ c, ∀ x, f x = c   :=  by sorry
