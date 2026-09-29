-- Prove2me | Theorems.Thm_lean_workbook_plus_21183
-- name    : lean_workbook_plus_21183
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/8cadae95-6fd8-4d67-b828-aa120dd0a246
-- statement:
--   Prove that $ 3^{2n + 1} + 2^{n + 2}$ is divisible by $ 7$ for all positive integers $ n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21183 : ∀ n : ℕ, 7 ∣ (3^(2 * n + 1) + 2^(n + 2))   :=  by sorry
