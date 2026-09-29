-- Prove2me | Theorems.Thm_lean_workbook_plus_70602
-- name    : lean_workbook_plus_70602
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/94bc85cf-5a6f-4da8-b6c5-ff68ee71a52a
-- statement:
--   This means that $ x \in (0,\frac {1}{2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70602  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x < 1 / 2) :
  x ∈ Set.Ioo 0 (1 / 2)   :=  by sorry
