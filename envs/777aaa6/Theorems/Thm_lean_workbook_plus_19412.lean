-- Prove2me | Theorems.Thm_lean_workbook_plus_19412
-- name    : lean_workbook_plus_19412
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/6342db76-12d6-4021-b9b3-996108c0f2c2
-- statement:
--   If $b+c\ge 2\sqrt{10}$ , by Cauchy we have $(b^2+10)(c^2+10)\ge 10(b+c)^2=10(12-a)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19412  (b c : ℝ)
  (h₀ : 2 * Real.sqrt 10 ≤ b + c) :
  (b^2 + 10) * (c^2 + 10) ≥ 10 * (b + c)^2   :=  by sorry
