-- Prove2me | Theorems.Thm_lean_workbook_plus_35572
-- name    : lean_workbook_plus_35572
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/809ddde2-37e6-4be5-a9fe-c3bb659950ee
-- statement:
--   prove that: \n $ (a^2c+b^2a+c^2b-a^2b-b^2c-c^2a)=(b-a)(c-a)(c-b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35572 : ∀ a b c : ℂ, (a^2*c + b^2*a + c^2*b - a^2*b - b^2*c - c^2*a) = (b - a) * (c - a) * (c - b)   :=  by sorry
