-- Prove2me | Theorems.Thm_lean_workbook_plus_2555
-- name    : lean_workbook_plus_2555
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/bcfbff16-6634-4ba2-af5b-410093698f16
-- statement:
--   Prove that for all reals $\alpha$ , $\beta$ and $\gamma$:\n$$\sin\alpha\sin\beta\sin\gamma\sin(\alpha+\beta+\gamma)=\sin\alpha\sin\gamma\sin(\alpha+\beta)\sin(\beta+\gamma)-\sin^2\alpha\sin^2\gamma$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2555 (α β γ : ℝ) :
  sin α * sin β * sin γ * sin (α + β + γ) =
  sin α * sin γ * sin (α + β) * sin (β + γ) -
  sin α ^ 2 * sin γ ^ 2   :=  by sorry
