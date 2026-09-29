-- Prove2me | Theorems.Thm_lean_workbook_plus_57584
-- name    : lean_workbook_plus_57584
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/3695a2bf-1b64-4b4f-85a7-92edcefde0be
-- statement:
--   Let the segments be $a,b,c$ with $a<b<c$ . Then $b=2a$ and $c=2a+0.5+x$ , where $x$ is some non-negative quantity. Then $a+b+c=6\implies 5a+0.5+x=6\implies a=1.1-{x\over 5}$ . This in turn yields $b=2.2-{2x\over 5}$ and $c=2.7+{3x\over 5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57584  (x a b c : ℝ)
  (h₀ : 0 ≤ x)
  (h₁ : a < b ∧ b < c)
  (h₂ : a + b + c = 6)
  (h₃ : b = 2 * a)
  (h₄ : c = 2 * a + 0.5 + x) :
  a = 1.1 - x / 5 ∧ b = 2.2 - 2 * x / 5 ∧ c = 2.7 + 3 * x / 5   :=  by sorry
