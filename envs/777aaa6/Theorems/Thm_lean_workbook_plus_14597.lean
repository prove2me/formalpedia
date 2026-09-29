-- Prove2me | Theorems.Thm_lean_workbook_plus_14597
-- name    : lean_workbook_plus_14597
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/2a16bd52-214e-466e-a9b5-dd6907e60b39
-- statement:
--   Prove that for all $a,b$ , if $ab=0$ then $ba=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14597 (a b : ℝ) (hab : a * b = 0) : b * a = 0   :=  by sorry
