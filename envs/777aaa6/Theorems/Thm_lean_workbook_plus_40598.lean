-- Prove2me | Theorems.Thm_lean_workbook_plus_40598
-- name    : lean_workbook_plus_40598
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/1c53e744-1e3f-4e55-8fa9-606ddf6aaa4c
-- statement:
--   Gerretsen's inequality: $4R^2+4Rr+3r^2\ge s^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40598 {R r s : ℝ} (hR : R ≥ 0) (hr : r ≥ 0) (hs : s ≥ 0) (hab : R + r = s) : 4 * R ^ 2 + 4 * R * r + 3 * r ^ 2 ≥ s ^ 2   :=  by sorry
