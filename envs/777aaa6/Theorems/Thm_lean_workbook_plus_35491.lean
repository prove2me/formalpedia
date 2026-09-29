-- Prove2me | Theorems.Thm_lean_workbook_plus_35491
-- name    : lean_workbook_plus_35491
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/0bcf7453-c59d-4e64-8b5e-d4c3e3d0232a
-- statement:
--   Let $ x = \frac{a}{b}; y = \frac{b}{c}; z = \frac{c}{a}$ We are asked to prove that $ a^2+b^2+c^2 \ge ab+bc+ca$ \nwhich is true as $ \frac{1}{2}(\sum (a-b)^2) \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35491  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : x = a / b)
  (h₁ : y = b / c)
  (h₂ : z = c / a) :
  a^2 + b^2 + c^2 ≥ a * b + b * c + c * a   :=  by sorry
