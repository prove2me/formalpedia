-- Prove2me | Theorems.Thm_lean_workbook_plus_61217
-- name    : lean_workbook_plus_61217
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/98723c58-c35e-4f49-8720-e250cdd9e695
-- statement:
--   Let $n\in \mathbb {N}$ and $n\geq 2$ . Prove that : $32\cdot n^{2n}\cdot (2n+1)>9\cdot (n+1)^{2n+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61217 : ∀ n : ℕ, 2 ≤ n → 32 * n^(2 * n) * (2 * n + 1) > 9 * (n + 1)^(2 * n + 1)   :=  by sorry
