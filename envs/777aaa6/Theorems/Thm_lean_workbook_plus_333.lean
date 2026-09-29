-- Prove2me | Theorems.Thm_lean_workbook_plus_333
-- name    : lean_workbook_plus_333
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/6465314b-4b8a-4532-85d0-ab2eba512217
-- statement:
--   If $f(c)=0=c(c+1)$ then $c=0$ or $c=-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_333 (c : ℂ) (f : ℂ → ℂ) (hf: f c = 0) (h : c * (c + 1) = 0) : c = 0 ∨ c = -1   :=  by sorry
