-- Prove2me | Theorems.Thm_lean_workbook_plus_27916
-- name    : lean_workbook_plus_27916
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/87189a82-88d2-4348-83eb-ab1709a67129
-- statement:
--   Because $ f$ is strictly increasing and $ f\left({\left[{0,\,1}\right]}\right)=\left[{0,\,1}\right]$ , then $ f(0)=0$ and $ f(1)=1$ . If $ g(0)=0$ or $ g(1)=1$ , then $ g(0)=0=f(0)$ or $ g(1)=1=f(1)$ . If $ g(0)\neq0$ and $ g(1)\neq1$ , because $ g\left({\left[{0,\,1}\right]}\right)=\left[{0,\,1}\right]$ , then $ g(0)>0$ and $ g(1)<1$ . For the continuous in $ \left[{0,\,1}\right]$ function $ g$ there is $ ^{(*)}$ $ x_0\in\left({0,\,1}\right)$ , such that $ g(x_0)=x_0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27916  (f g : ℝ → ℝ)
  (h₁ : Continuous g)
  (h₂ : 0 ≤ g ∧ g ≤ 1)
  (h₃ : ∀ x y, 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 → x ≤ y → f x ≤ f y)
  (h₄ : ∀ x y, 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 → x < y → f x < f y)
  (h₅ : g 0 = 0 ∨ g 1 = 1)
  (h₆ : f 0 = 0 ∧ f 1 = 1) :
  ∃ x, g x = x   :=  by sorry
