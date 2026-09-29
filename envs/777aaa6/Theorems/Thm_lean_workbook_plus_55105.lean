-- Prove2me | Theorems.Thm_lean_workbook_plus_55105
-- name    : lean_workbook_plus_55105
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/f795d3cc-95dc-424b-acc3-53cfada43d3c
-- statement:
--   Prove that there is no surjective function from a set $E$ to its power set $P(E)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55105 (E : Type) : ¬∃ f : E → Set E, Function.Surjective f   :=  by sorry
