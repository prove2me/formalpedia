-- Prove2me | Theorems.Thm_lean_workbook_plus_21277
-- name    : lean_workbook_plus_21277
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/2e4fe868-2be0-44b3-8a5f-79d56de4a6c2
-- statement:
--   Prove that $f(a) = -f(-a)$ for all $a \in \mathbb{R}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21277 (f : ℝ → ℝ) (hf : ∀ a, f a + f (-a) = 0) : ∀ a, f a = -f (-a)   :=  by sorry
