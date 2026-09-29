-- Prove2me | Theorems.Thm_lean_workbook_plus_17325
-- name    : lean_workbook_plus_17325
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/aab650ad-da2e-42d5-8406-a888d48504e8
-- statement:
--   Suppose that $ac=0$ and $a \ne 0$. Prove that $c=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17325 (a c : ℝ) (h₁ : a ≠ 0) (h₂ : a * c = 0) : c = 0   :=  by sorry
