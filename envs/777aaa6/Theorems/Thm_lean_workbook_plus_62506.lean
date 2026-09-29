-- Prove2me | Theorems.Thm_lean_workbook_plus_62506
-- name    : lean_workbook_plus_62506
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/71f62b66-79d6-461f-8468-240e01feeee1
-- statement:
--   Prove that: $(n!)^{\frac{1}{n}}\ge n^{\frac{1}{2}}\forall n\in \mathbb{N}^*$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62506 : ∀ n : ℕ, (n!)^(1 / n) ≥ √n   :=  by sorry
