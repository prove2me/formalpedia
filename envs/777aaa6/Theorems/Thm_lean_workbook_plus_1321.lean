-- Prove2me | Theorems.Thm_lean_workbook_plus_1321
-- name    : lean_workbook_plus_1321
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/0ebc0a2a-d0b5-4f2e-a382-1c59c96ae4b7
-- statement:
--   The function $f(x)$ is strictly decreasing; $f(0)=1;f(1)=0\Longrightarrow f(x)\in(0,1),\;\forall x\in(0,1)\Longrightarrow x_n\in(0,1),\;\forall n\in\mathbb{N}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1321  (f : ℝ → ℝ)
  (h₀ : StrictAnti f)
  (h₁ : f 0 = 1)
  (h₂ : f 1 = 0)
  : ∀ x ∈ Set.Ioo 0 1, 0 < f x ∧ f x < 1   :=  by sorry
