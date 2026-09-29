-- Prove2me | Theorems.Thm_lean_workbook_plus_15056
-- name    : lean_workbook_plus_15056
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/433665b4-664f-4aaf-ae6a-704048969a9c
-- statement:
--   Prove that $0\le (1-\sin x)(1-\sin y)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15056 : ∀ x y : ℝ, 0 ≤ (1 - Real.sin x) * (1 - Real.sin y)   :=  by sorry
