-- Prove2me | Theorems.Thm_lean_workbook_plus_59732
-- name    : lean_workbook_plus_59732
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/7e3d686d-7df7-4cda-9ab7-53adfff9bd6c
-- statement:
--   $\frac{3}{\sqrt7}=\frac{3\sqrt7}{7}$ , $\frac{2}{\sqrt6}=\frac{\sqrt6}{3}$ . Subtract to get $\frac{9\sqrt7-7\sqrt6}{21}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59732 :
  3 / Real.sqrt 7 - 2 / Real.sqrt 6 = (9 * Real.sqrt 7 - 7 * Real.sqrt 6) / 21   :=  by sorry
