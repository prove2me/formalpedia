-- Prove2me | Theorems.Thm_lean_workbook_plus_70415
-- name    : lean_workbook_plus_70415
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/5cec0917-a903-4de3-a497-9a5e7fd8b12f
-- statement:
--   Put $a=xyz-{1\over xyz}$ . Then $x-{1\over y}={a\over 6}, y-{1\over z}={a\over 3}, z-{1\over x}={a\over 2}$ . Summing up those three we get $x+y+z-{1\over x}-{1\over y}-{1\over z}=a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70415  (x y z : ℝ)
  (a : ℝ)
  (h₀ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0)
  (h₁ : a = x * y * z - 1 / (x * y * z))
  (h₂ : x - 1/y = a/6)
  (h₃ : y - 1/z = a/3)
  (h₄ : z - 1/x = a/2)
  (h₅ : 0 < x ∧ 0 < y ∧ 0 < z) :
  x + y + z - 1/x - 1/y - 1/z = a   :=  by sorry
