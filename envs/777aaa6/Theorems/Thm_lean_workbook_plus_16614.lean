-- Prove2me | Theorems.Thm_lean_workbook_plus_16614
-- name    : lean_workbook_plus_16614
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/baabbc6d-f39a-411f-9d5c-c695942131e3
-- statement:
--   Let $x$ and $y$ be integers. Prove that $2x + 3y$ is divisible by $17$ if $9x + 5y$ is divisible by $17$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16614 : ∀ x y : ℤ, 17 ∣ 9 * x + 5 * y → 17 ∣ 2 * x + 3 * y   :=  by sorry
