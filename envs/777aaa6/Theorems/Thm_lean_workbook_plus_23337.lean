-- Prove2me | Theorems.Thm_lean_workbook_plus_23337
-- name    : lean_workbook_plus_23337
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/05fe7fc5-510e-4247-97cd-8ac209dc96cb
-- statement:
--   Prove that the function $T(n) = 2n - 2 - \log{n}$ is $\Theta(n)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23337 : ∃ (c1 c2 : ℝ), 0 < c1 ∧ 0 < c2 ∧ ∀ n : ℕ, c1 * n ≤ 2 * n - 2 - Real.log n ∧ 2 * n - 2 - Real.log n ≤ c2 * n   :=  by sorry
