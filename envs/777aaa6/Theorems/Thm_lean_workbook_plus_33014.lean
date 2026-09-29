-- Prove2me | Theorems.Thm_lean_workbook_plus_33014
-- name    : lean_workbook_plus_33014
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c599bbc6-24a2-4a2a-a7bd-3cf47cce31f5
-- statement:
--   $ \sqrt{\sqrt{n}+n+2} < \sqrt{n+1}+1 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33014 (n : ℕ) : Real.sqrt (Real.sqrt n + n + 2) < Real.sqrt (n + 1) + 1   :=  by sorry
