-- Prove2me | Theorems.Thm_lean_workbook_plus_10773
-- name    : lean_workbook_plus_10773
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/47a0a9d9-974d-4bf0-b0d9-1e1f46e44062
-- statement:
--   $\frac{\sqrt{2-\sqrt{2}}}{2} =\frac{\sqrt{2}}{2}\cdot \sqrt{1-\frac{\sqrt{2}}{2}}=\frac{\sqrt{2}}{2}\cdot \sqrt{1-\cos\frac{\pi}{4}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10773 : (Real.sqrt (2 - Real.sqrt 2)) / 2 = (Real.sqrt 2 / 2) * Real.sqrt (1 - Real.sqrt 2 / 2)   :=  by sorry
