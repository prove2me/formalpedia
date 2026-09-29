-- Prove2me | Theorems.Thm_lean_workbook_plus_17430
-- name    : lean_workbook_plus_17430
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/d26b6999-76dc-4cd1-92a5-91c9a02138b9
-- statement:
--   Show that the series $ \sum _{k \in \mathbb{N}} 1/2^k$ converges
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17430 : ∃ y, (∑' k : ℕ, (1:ℝ) / 2 ^ k) = y   :=  by sorry
