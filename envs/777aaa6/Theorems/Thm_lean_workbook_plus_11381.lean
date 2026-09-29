-- Prove2me | Theorems.Thm_lean_workbook_plus_11381
-- name    : lean_workbook_plus_11381
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/9ce39302-3cb6-4835-a2f4-fd795376899b
-- statement:
--   If $xy+yz+zx=k$ ,where $k,x,y,z\in {{\mathbb{R}}^{*}}$ with $\left( x+y \right)\left( y+z \right)\left( z+x \right)\ne 0$ ,then: \n $\frac{{{x}^{2}}+{{y}^{2}}+2k}{x+y}+\frac{{{y}^{2}}+{{z}^{2}}+2k}{y+z}+\frac{{{z}^{2}}+{{x}^{2}}+2k}{z+x}=4\left( x+y+z \right)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11381    (x y z k : ℝ)
    (h₀ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0)
    (h₁ : x + y ≠ 0)
    (h₂ : y + z ≠ 0)
    (h₃ : z + x ≠ 0)
    (h₄ : x * y + y * z + z * x = k) :
    (x^2 + y^2 + 2 * k) / (x + y) + (y^2 + z^2 + 2 * k) / (y + z) + (z^2 + x^2 + 2 * k) / (z + x) = 4 * (x + y + z)   :=  by sorry
