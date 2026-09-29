-- Prove2me | Theorems.Thm_lean_workbook_plus_56852
-- name    : lean_workbook_plus_56852
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/4b0e280f-2cce-444e-af45-d198d86d6ddc
-- statement:
--   Given $f: \mathbb{R}\rightarrow \mathbb{R}$, prove that if $f(f(x)) = x$ for all $x \in \mathbb{R}$, then $f$ is bijective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56852 (f : ℝ → ℝ) (hf: f ∘ f = id) : Function.Bijective f   :=  by sorry
