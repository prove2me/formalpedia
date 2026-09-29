-- Prove2me | Theorems.Thm_lean_workbook_plus_28104
-- name    : lean_workbook_plus_28104
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/d8b67feb-f3d6-410b-a551-272fc5dc2c72
-- statement:
--   Prove that $\forall n\in\mathbb{N}$ $19|7^{6n + 2} + 7^{3n + 1} + 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28104 : ∀ n : ℕ, 19 ∣ 7^(6 * n + 2) + 7^(3 * n + 1) + 1   :=  by sorry
