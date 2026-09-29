-- Prove2me | Theorems.Thm_lean_workbook_plus_63077
-- name    : lean_workbook_plus_63077
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/aef80466-7bf4-4bf5-83c3-e748f8a7db83
-- statement:
--   I am sorry, it should be stated that $ p$ is prime and $ m$ integer. Thank you riddler
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63077 (p : ℕ) (hp : p.Prime) (m : ℤ) : (∃ n : ℕ, (n : ℤ)^2 = m * p) ↔ ∃ t : ℤ, t^2 = m * p   :=  by sorry
