-- Prove2me | Theorems.Thm_lean_workbook_plus_8045
-- name    : lean_workbook_plus_8045
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/a4e23f2b-3824-4f66-ae8b-ed267c896b5a
-- statement:
--   We can also use conditional probability: We want to find the value of $P(\text{genetically modified}|\text{sprouts})$. We know this is equal to $\frac{P(\text{genetically modified and sprouts})}{P(\text{sprouts})}$ which in turn is $\frac{\frac{2}{5}\cdot\frac{1}{2}}{\frac{2}{5}\cdot\frac{1}{2}+\frac{3}{5}\cdot\frac{1}{3}}$, or simply $\boxed{\frac{1}{2}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8045  (p q r s : ℝ)
  (h₀ : p = 2 / 5)
  (h₁ : q = 1 / 2)
  (h₂ : r = 3 / 5)
  (h₃ : s = 1 / 3)
  (h₄ : p * q = r * s) :
  p * q / (p * q + r * s) = 1 / 2   :=  by sorry
