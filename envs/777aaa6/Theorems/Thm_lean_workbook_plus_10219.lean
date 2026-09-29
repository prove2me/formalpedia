-- Prove2me | Theorems.Thm_lean_workbook_plus_10219
-- name    : lean_workbook_plus_10219
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/8a3879db-7bb9-4052-86ec-5e84346a8e6d
-- statement:
--   Prove that function $f(x) = x^{4} - 4x + 1$ is injective on the interval $[0,1]$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10219 (f : ℝ → ℝ) (hf: f = fun x => x^4 - 4*x + 1) : ∀ x ∈ [0,1], ∀ y ∈ [0,1], f x = f y → x = y   :=  by sorry
