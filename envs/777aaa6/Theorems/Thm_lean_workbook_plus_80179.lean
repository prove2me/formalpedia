-- Prove2me | Theorems.Thm_lean_workbook_plus_80179
-- name    : lean_workbook_plus_80179
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b3f33d77-b863-42bf-810f-33ba41a8c9cf
-- statement:
--   Hello, it reduces to $$\frac{b+c}{2}\geq \sqrt{bc}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80179 (b c : ℝ) (hb : 0 < b) (hc : 0 < c) : (b + c) / 2 ≥ Real.sqrt (b * c)   :=  by sorry
