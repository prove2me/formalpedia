-- Prove2me | Theorems.Thm_lean_workbook_plus_18397
-- name    : lean_workbook_plus_18397
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/64be9531-2acc-4be0-af4e-6624ff48dbe8
-- statement:
--   Prove that $sin(x)^{sin(x)}<cos(x)^{cos(x)} with 0\le x \le\frac{pi}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18397 : ∀ x : ℝ, x ∈ Set.Icc 0 (Real.pi / 4) → sin x ^ sin x < cos x ^ cos x   :=  by sorry
