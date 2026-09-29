-- Prove2me | Theorems.Thm_lean_workbook_plus_82183
-- name    : lean_workbook_plus_82183
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e6d2a932-9d9e-4337-b166-1bd63a41b16c
-- statement:
--   Prove that if $ x,y,z$ are real numbers and $ x+y+z=2$ and $ xy+yz+zx=1$ then $ x,y,z \in [0,\frac{4}{3}]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82183 (x y z : ℝ) (h₁ : x + y + z = 2) (h₂ : x * y + y * z + z * x = 1) : x ∈ Set.Icc 0 (4/3) ∧ y ∈ Set.Icc 0 (4/3) ∧ z ∈ Set.Icc 0 (4/3)   :=  by sorry
