-- Prove2me | Theorems.Thm_lean_workbook_plus_22006
-- name    : lean_workbook_plus_22006
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/5bf2bf6b-e478-4350-9acd-52a2a99bb32d
-- statement:
--   We can solve this quadratic for d. The result is $d^2+4d-140=(d+14)(d-10)=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22006  (d : ℝ)
  (h₀ : d^2 + 4 * d - 140 = 0) :
  (d + 14) * (d - 10) = 0   :=  by sorry
