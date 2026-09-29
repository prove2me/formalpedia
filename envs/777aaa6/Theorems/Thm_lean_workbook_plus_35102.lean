-- Prove2me | Theorems.Thm_lean_workbook_plus_35102
-- name    : lean_workbook_plus_35102
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/88589960-34b3-4144-bde9-99ca869bc439
-- statement:
--   Prove that for $x \geq 0$, $\sqrt{x} \leq \frac{1}{2}(x - 1) + 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35102 (x : ℝ) (hx : 0 ≤ x) : √x ≤ (1 / 2) * (x - 1) + 1   :=  by sorry
