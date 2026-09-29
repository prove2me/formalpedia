-- Prove2me | Theorems.Thm_lean_workbook_plus_40220
-- name    : lean_workbook_plus_40220
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/e192275c-8c63-436d-976b-2463e7772b8f
-- statement:
--   $P(0,0)$ $\implies$ $f(f(0))=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40220 (f : ℝ → ℝ): f 0 = 0 → f (f 0) = 0   :=  by sorry
