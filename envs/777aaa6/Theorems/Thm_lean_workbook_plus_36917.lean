-- Prove2me | Theorems.Thm_lean_workbook_plus_36917
-- name    : lean_workbook_plus_36917
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/cff34a15-9bb8-45cd-b0d7-c00e4182dcfa
-- statement:
--   Show that $(A \times B) \setminus (A\times C) \supseteq A\times (B \setminus C)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36917 (A B C : Set α) : (A ×ˢ B) \ (A ×ˢ C) ⊇ A ×ˢ (B \ C)   :=  by sorry
