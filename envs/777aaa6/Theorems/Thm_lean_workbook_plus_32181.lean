-- Prove2me | Theorems.Thm_lean_workbook_plus_32181
-- name    : lean_workbook_plus_32181
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/4ef74546-c59d-44ea-a619-169d0c0c3340
-- statement:
--   Prove that for all x, y: if $x \geq 0$ and $y \geq 0$, then $\sqrt{x}\sqrt{y} = \sqrt{xy}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32181 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : Real.sqrt x * Real.sqrt y = Real.sqrt (x * y)   :=  by sorry
