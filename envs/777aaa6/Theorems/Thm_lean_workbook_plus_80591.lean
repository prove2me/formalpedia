-- Prove2me | Theorems.Thm_lean_workbook_plus_80591
-- name    : lean_workbook_plus_80591
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/6a560d2f-a23d-4d8f-b794-d266aace1622
-- statement:
--   $\implies \log x=\log 6 \implies x=6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80591  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : Real.log x = Real.log 6) :
  x = 6   :=  by sorry
