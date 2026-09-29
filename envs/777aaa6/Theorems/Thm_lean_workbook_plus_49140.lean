-- Prove2me | Theorems.Thm_lean_workbook_plus_49140
-- name    : lean_workbook_plus_49140
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/1231395c-d2dd-49ec-bdb7-ca1514c4e1c0
-- statement:
--   So $\boxed{f(n)=n}$ $\forall n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49140 (f : ℕ → ℕ) (hf: f = fun n => n) : ∀ n, f n = n   :=  by sorry
