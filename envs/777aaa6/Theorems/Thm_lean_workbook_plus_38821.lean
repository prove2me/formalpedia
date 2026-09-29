-- Prove2me | Theorems.Thm_lean_workbook_plus_38821
-- name    : lean_workbook_plus_38821
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/768aadd2-ad50-483d-b6fb-bb79035e17e0
-- statement:
--   Prove that $(3+\sqrt5)^{n}+(3-\sqrt5)^{n}$ is divisible by $2^{n}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38821 (n : ℕ) : 2 ^ n ∣ (3 + Real.sqrt 5) ^ n + (3 - Real.sqrt 5) ^ n   :=  by sorry
