-- Prove2me | Theorems.Thm_lean_workbook_plus_67386
-- name    : lean_workbook_plus_67386
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/5a972d7b-00bf-40bf-baa5-28b934f8eb77
-- statement:
--   1) $\lfloor x+2\rfloor=-2$ (and so $x\in[-4,-3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67386 (x : ℝ) (hx : ⌊x + 2⌋ = -2) : x ∈ Set.Icc (-4) (-3)   :=  by sorry
