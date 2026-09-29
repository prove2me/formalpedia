-- Prove2me | Theorems.Thm_lean_workbook_plus_40067
-- name    : lean_workbook_plus_40067
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/d3a7a27a-7a69-4c7c-b62f-8c88e24d2779
-- statement:
--   Prove $\lfloor 2a+2b \rfloor\ge\lfloor a+b \rfloor$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40067 : ∀ a b : ℝ, Int.floor (2 * a + 2 * b) ≥ Int.floor (a + b)   :=  by sorry
