-- Prove2me | Theorems.Thm_lean_workbook_plus_61362
-- name    : lean_workbook_plus_61362
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/7d3b844b-c28f-4c0e-9a2a-6dabcbb8e678
-- statement:
--   $\frac{st}{r}$ is integer , so $\frac{s^2t^2}{r^2}$ is integer too.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61362 (r s t : ℤ) (h : r ≠ 0)  (h2 : r∣s*t) : r^2 ∣ s^2 * t^2   :=  by sorry
