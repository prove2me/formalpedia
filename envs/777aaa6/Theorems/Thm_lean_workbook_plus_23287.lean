-- Prove2me | Theorems.Thm_lean_workbook_plus_23287
-- name    : lean_workbook_plus_23287
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/e3646234-b9b8-4d2a-85cf-cc3f74a63b32
-- statement:
--   Prove that for even values of positive n, $2^n-1$ is congruent to $1 \pmod 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23287 : ∀ n : ℕ, Even n ∧ n > 0 → (2^n - 1 ≡ 1 [ZMOD 3])   :=  by sorry
