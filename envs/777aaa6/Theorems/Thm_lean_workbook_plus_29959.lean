-- Prove2me | Theorems.Thm_lean_workbook_plus_29959
-- name    : lean_workbook_plus_29959
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/50ef8e1b-d6c7-4002-b7bf-ae9fad1a6b26
-- statement:
--   $(2)$ $ \lfloor x\rfloor -2 \lfloor \frac{x}{2}\rfloor<2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29959 : ∀ x : ℝ, (Int.floor x - 2 * Int.floor (x / 2)) < 2   :=  by sorry
