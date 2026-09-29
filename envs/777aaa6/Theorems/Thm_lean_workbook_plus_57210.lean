-- Prove2me | Theorems.Thm_lean_workbook_plus_57210
-- name    : lean_workbook_plus_57210
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/27319b25-6d00-4e7e-bd81-fcc95ead5d5e
-- statement:
--   What values of $x$ satisfy the equation $0 = x \cdot 0$ for all $x \in \mathbb{C}$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57210 (x : ℂ) : 0 = x * 0 ↔ x ∈ Set.univ   :=  by sorry
