-- Prove2me | Theorems.Thm_lean_workbook_plus_30088
-- name    : lean_workbook_plus_30088
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/746bd68b-a33c-49e5-b45a-f0326e05d297
-- statement:
--   A/Q $ n,m$ both odd. $ n-m$ must be even.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30088 : ∀ n m : ℤ, Odd n ∧ Odd m → Even (n - m)   :=  by sorry
