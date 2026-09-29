-- Prove2me | Theorems.Thm_lean_workbook_plus_39394
-- name    : lean_workbook_plus_39394
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/5cfe4426-22b8-49de-8e22-089a5f0de6e4
-- statement:
--   prove that the greatest integer less than $(1+\sqrt{3})^{2n}$ is divisible by $2^{n+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39394 (n : ℕ) : ∃ k : ℕ, (2 : ℝ)^(n+1) ∣ (1 + Real.sqrt 3)^(2 * n) - k   :=  by sorry
