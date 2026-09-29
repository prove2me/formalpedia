-- Prove2me | Theorems.Thm_lean_workbook_plus_76620
-- name    : lean_workbook_plus_76620
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/66dd3bfc-4bd7-456c-abdc-9a1ad40079a4
-- statement:
--   If $a\geqq b\geqq c, x\geqq y\geqq z, x+y+z=0$ , prove that we have $ax+by+cz\geqq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76620 (a b c x y z : ℝ) (h₁ : a ≥ b ∧ b ≥ c) (h₂ : x ≥ y ∧ y ≥ z) (h₃ : x + y + z = 0) : a * x + b * y + c * z ≥ 0   :=  by sorry
