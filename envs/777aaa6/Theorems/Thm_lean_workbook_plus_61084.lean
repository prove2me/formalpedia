-- Prove2me | Theorems.Thm_lean_workbook_plus_61084
-- name    : lean_workbook_plus_61084
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/985d64c6-fc9c-43cf-b766-480b57c60539
-- statement:
--   Let $0<x\leq y\leq z$ . Prove that $(x+y+z)(xy+yz+zx) \geq 9xyz+(y-x)(z-x)^{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61084  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x ≤ y ∧ y ≤ z) :
  (x + y + z) * (x*y + y*z + z*x) ≥ 9*x*y*z + (y - x)*(z - x)^2   :=  by sorry
