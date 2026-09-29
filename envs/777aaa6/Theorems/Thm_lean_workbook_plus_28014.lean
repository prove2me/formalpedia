-- Prove2me | Theorems.Thm_lean_workbook_plus_28014
-- name    : lean_workbook_plus_28014
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/72bea015-2248-499f-b952-ec8755e51b16
-- statement:
--   If $0\le z\le 1$ , then $z\ge z^2$ and $z=z^2\to z=0$ or $z=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28014 (z : ℝ) (hz: 0 ≤ z ∧ z ≤ 1) : z ≥ z^2 ∧ (z = z^2 ↔ z = 0 ∨ z = 1)   :=  by sorry
