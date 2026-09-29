-- Prove2me | Theorems.Thm_lean_workbook_plus_44680
-- name    : lean_workbook_plus_44680
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/695faa44-bf1c-44be-8fc3-bdd2911cd266
-- statement:
--   $ \implies xy-x-y-1=0 \implies (x-1)(y-1)=2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44680  (x y : ℂ)
  (h₀ : x * y - x - y - 1 = 0) :
  (x - 1) * (y - 1) = 2   :=  by sorry
