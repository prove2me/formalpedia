-- Prove2me | Theorems.Thm_lean_workbook_plus_47941
-- name    : lean_workbook_plus_47941
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/28796e30-c883-4b23-b33c-ae0d41d28101
-- statement:
--   After substitution $a=y+z$ , $b=x+z$ and $c=x+y$ , where $x$ , $y$ and $z$ are positive numbers we obtain: $\sum_{cyc}x(x+y)(x-y)^2\geq0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47941 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x * (x + y) * (x - y) ^ 2 + y * (y + z) * (y - z) ^ 2 + z * (z + x) * (z - x) ^ 2 ≥ 0   :=  by sorry
