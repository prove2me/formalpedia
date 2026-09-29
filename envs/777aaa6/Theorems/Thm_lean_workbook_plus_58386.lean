-- Prove2me | Theorems.Thm_lean_workbook_plus_58386
-- name    : lean_workbook_plus_58386
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/c40952d0-58ab-4102-9f5b-7e59a4860891
-- statement:
--   but if $P(n)=n+3$ then $P(17)=17+3=20$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58386 (P : ℕ → ℕ) (h : P = fun (n:ℕ) => n + 3) : P 17 = 20   :=  by sorry
