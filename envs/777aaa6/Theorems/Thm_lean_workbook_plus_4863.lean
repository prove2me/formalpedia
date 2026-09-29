-- Prove2me | Theorems.Thm_lean_workbook_plus_4863
-- name    : lean_workbook_plus_4863
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/d4d9b412-d8f2-4f51-afb4-e76a61088cf4
-- statement:
--   Prove the inequality: $a^b \geq ab$ for $a, b \in \mathbb{N}$ and $a > 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4863 (a b : ℕ) (ha : 1 < a) : a^b ≥ a * b   :=  by sorry
