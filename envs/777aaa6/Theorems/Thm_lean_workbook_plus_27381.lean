-- Prove2me | Theorems.Thm_lean_workbook_plus_27381
-- name    : lean_workbook_plus_27381
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/7f85959b-4324-405c-90dc-d5fca0a3114c
-- statement:
--   Prove that the function $f: \mathbb{N}^* \rightarrow \mathbb{N}^*$ defined by $f(n) = n^2 + n + 1$ is surjective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27381 : ∀ n : ℕ, n ∈ Set.range (fun n : ℕ => n^2 + n + 1)   :=  by sorry
