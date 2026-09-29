-- Prove2me | Theorems.Thm_lean_workbook_plus_58491
-- name    : lean_workbook_plus_58491
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/f9f44994-572d-4b58-941e-60a008a9c6f8
-- statement:
--   Suppose Bridge bought $ x$ apples. Then, after giving apples to Ann, she has $ \dfrac{x}{2}$ apples left. After giving Cassie 3 apples, she has $ \dfrac{x}{2}-3$ apples. Because she has 4 apples left, $ \dfrac{x}{2}-3=4 \implies x=14$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58491  (x : ℝ)
  (h₀ : x / 2 - 3 = 4) :
  x = 14   :=  by sorry
