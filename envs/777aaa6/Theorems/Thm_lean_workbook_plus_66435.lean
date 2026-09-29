-- Prove2me | Theorems.Thm_lean_workbook_plus_66435
-- name    : lean_workbook_plus_66435
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e9a0c10d-5e95-41ba-8546-d9d96cab8bf2
-- statement:
--   If $n|2^{n}-3$ , then $1489\not | n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66435 : ∀ n : ℕ, n ∣ (2 ^ n - 3) → ¬ 1489 ∣ n   :=  by sorry
