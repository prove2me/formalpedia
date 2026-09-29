-- Prove2me | Theorems.Thm_lean_workbook_plus_81538
-- name    : lean_workbook_plus_81538
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/41ebce26-6533-400c-bf08-4864bfe89719
-- statement:
--   $\sqrt{\frac{a^{2}}{4}}\geq \sqrt{a-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81538 (a : ℝ) (ha : 0 ≤ a) : Real.sqrt (a^2 / 4) ≥ Real.sqrt (a - 1)   :=  by sorry
