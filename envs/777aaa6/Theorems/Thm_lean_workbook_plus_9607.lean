-- Prove2me | Theorems.Thm_lean_workbook_plus_9607
-- name    : lean_workbook_plus_9607
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/93a28dcc-5bdd-42c9-b8d3-3b1e3392b5dc
-- statement:
--   Prove that the roots of the equation $\sin x = 0$ are $n\pi$ where $n \in \mathbb{Z}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9607 (x : ℝ) : sin x = 0 ↔ ∃ n : ℤ, x = n * π   :=  by sorry
