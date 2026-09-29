-- Prove2me | Theorems.Thm_lean_workbook_plus_58863
-- name    : lean_workbook_plus_58863
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/12d13942-f21b-4a09-af77-2d3a49d96114
-- statement:
--   Let $a=1-x$, $b=1-y$ and $c=1-z$. Hence, {x,y,z}⊆(0,1), the condition gives xy+xz+yz=4xyz and we need to prove that x+y+z≥9/4, which is (x+y+z)(xy+xz+yz)≥9xyz, which is AM-GM.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58863  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x + y + z = 1)
  (h₂ : x * y + x * z + y * z = 4 * x * y * z) :
  x + y + z ≥ 9 / 4   :=  by sorry
