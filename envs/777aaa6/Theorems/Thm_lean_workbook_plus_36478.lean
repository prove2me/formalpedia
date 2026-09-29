-- Prove2me | Theorems.Thm_lean_workbook_plus_36478
-- name    : lean_workbook_plus_36478
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/a5eb8775-e510-4cc5-b94e-4a624687dafa
-- statement:
--   Show that $2018(m + 2^k)^2 + 20182017(m + 2^k) + 2017$ is divisible by $2^{k+1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36478 : ∀ m k : ℕ, (2018 * (m + 2 ^ k) ^ 2 + 20182017 * (m + 2 ^ k) + 2017) % (2 ^ (k + 1)) = 0   :=  by sorry
