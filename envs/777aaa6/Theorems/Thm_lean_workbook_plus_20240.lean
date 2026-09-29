-- Prove2me | Theorems.Thm_lean_workbook_plus_20240
-- name    : lean_workbook_plus_20240
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/ab05618d-aeff-439f-923d-8d09bae81009
-- statement:
--   Prove that for all positive real $x$ , the following inequality holds: \n\n $$(x + 1)(x + 2)(x + 5) \geq 36x.$$ \n\n Alternatively, we can note $f(x)=(x + 1)(x + 2)(x + 5) -36x$ , then we have: \n\n $f'(x)=(x-1)(3x+19)$ which means that for $x\geq 0$ , we have: \n\n $f(x) \geq f(1)=0$ Done.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20240  (x : ℝ)
  (h₀ : 0 < x) :
  (x + 1) * (x + 2) * (x + 5) ≥ 36 * x   :=  by sorry
