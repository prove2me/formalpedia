-- Prove2me | Theorems.Thm_lean_workbook_plus_60537
-- name    : lean_workbook_plus_60537
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/569009cc-2cb9-4e40-b897-9d19035b5033
-- statement:
--   Schur's inequality $\sum_\text{cyc} a(a-b)(a-c) \geqslant 0$ is equivalent to $\sum_\text{cyc} 6a(a-b)(a-c) \geqslant 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60537 {a b c : ℝ} : a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) ≥ 0 ↔ 6 * a * (a - b) * (a - c) + 6 * b * (b - a) * (b - c) + 6 * c * (c - a) * (c - b) ≥ 0   :=  by sorry
