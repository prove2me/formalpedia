-- Prove2me | Theorems.Thm_lean_workbook_plus_2952
-- name    : lean_workbook_plus_2952
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/687a0461-9cda-41ff-9a77-8cd3a94b39cc
-- statement:
--   Equality when $ a=a , b=a+2 , c=a+1$ $\Box$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2952 (a b c : ℕ) (h₁ : a = a) (h₂ : b = a + 2) (h₃ : c = a + 1) : a + b + c = a + a + 2 + a + 1   :=  by sorry
