-- Prove2me | Theorems.Thm_lean_workbook_plus_48775
-- name    : lean_workbook_plus_48775
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/ab930690-225a-4b9f-962e-a93fd32ac05c
-- statement:
--   Show that : $2015 < \frac{2^2+1}{2^2-1} + \frac{3^2+1}{3^2-1} + ... + \frac{2015^2+1}{2015^2-1} < 2015 + \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48775 : 2015 < (∑ i in Finset.Icc 2 2015, (i^2 + 1) / (i^2 - 1)) ∧ (∑ i in Finset.Icc 2 2015, (i^2 + 1) / (i^2 - 1)) < 2015 + 1 / 2   :=  by sorry
