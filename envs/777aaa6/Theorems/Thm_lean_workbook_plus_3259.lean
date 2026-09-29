-- Prove2me | Theorems.Thm_lean_workbook_plus_3259
-- name    : lean_workbook_plus_3259
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/0c67b5d0-4aa0-48a1-a2be-707e64fccc91
-- statement:
--   What is the value of $x$ where $x = \sum_{e=1}^{5050}e$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3259 (x : ℕ) (hx : x = ∑ e in Finset.Icc 1 5050, e) : x = 12753775   :=  by sorry
