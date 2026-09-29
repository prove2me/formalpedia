-- Prove2me | Theorems.Thm_lean_workbook_plus_48501
-- name    : lean_workbook_plus_48501
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/80d63b46-d173-47f1-a754-af0d154db525
-- statement:
--   prove that: $n^4 \equiv 1 (mod$ $10)$, where $n$ is an odd positive integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48501 : ∀ n : ℕ, n % 2 = 1 → n ^ 4 % 10 = 1   :=  by sorry
