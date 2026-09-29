-- Prove2me | Theorems.Thm_lean_workbook_plus_43574
-- name    : lean_workbook_plus_43574
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/6d52e182-3dd7-4736-bf4b-81aaa0318cd1
-- statement:
--   Since $I+J = 4$ and $I-J = \pi$, we have that $I = \dfrac{4+\pi}{2}$ and $J = \dfrac{4-\pi}{2}$ as desired.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43574 (I J : ℝ) (h₁ : I + J = 4) (h₂ : I - J = Real.pi) : I = (4 + Real.pi) / 2 ∧ J = (4 - Real.pi) / 2   :=  by sorry
