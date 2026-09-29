-- Prove2me | Theorems.Thm_lean_workbook_plus_30119
-- name    : lean_workbook_plus_30119
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/efbe4d1e-d7a9-4bea-b760-b62a8bc0e64d
-- statement:
--   Prove that the inequality $\mid s+t \mid \leq \mid s \mid + \mid t \mid$ holds for any two complex numbers $s$ and $t$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30119 (s t : ℂ) : ‖s + t‖ ≤ ‖s‖ + ‖t‖   :=  by sorry
