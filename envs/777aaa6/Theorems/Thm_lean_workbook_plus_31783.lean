-- Prove2me | Theorems.Thm_lean_workbook_plus_31783
-- name    : lean_workbook_plus_31783
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/aba04437-3c8e-4744-aef7-93f6ec21bc1f
-- statement:
--   Prove that for all $t \in [0,\frac 1 2]$ we have $t^3 + (1-t)^3 - t^4 - (1-t)^4 \le \frac 1 8$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31783 ∀ t ∈ Set.Icc 0 (1/2), t^3 + (1-t)^3 - t^4 - (1-t)^4 ≤ 1/8   :=  by sorry
