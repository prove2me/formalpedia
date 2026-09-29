-- Prove2me | Theorems.Thm_lean_workbook_plus_72380
-- name    : lean_workbook_plus_72380
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/6ea47af8-9664-4cef-b2fb-cdb70af8010f
-- statement:
--   $\frac{a^{2}}{2}+\frac{a^{2}}{2}+\frac{e^{2}}{8}+\frac{e^{2}}{8}\geq ae$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72380 (a e : ℝ) :
  a^2 / 2 + a^2 / 2 + e^2 / 8 + e^2 / 8 ≥ a * e   :=  by sorry
