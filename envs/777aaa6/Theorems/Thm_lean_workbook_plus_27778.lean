-- Prove2me | Theorems.Thm_lean_workbook_plus_27778
-- name    : lean_workbook_plus_27778
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/3e95d753-d658-456f-b036-399c409d4826
-- statement:
--   Prove that if $p=6k+1$, then $2p-1$ is divisible by 3.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27778 : ∀ p : ℕ, p = 6 * k + 1 → 3 ∣ (2 * p - 1)   :=  by sorry
