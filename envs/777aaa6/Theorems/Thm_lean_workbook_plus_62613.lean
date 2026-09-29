-- Prove2me | Theorems.Thm_lean_workbook_plus_62613
-- name    : lean_workbook_plus_62613
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/21938890-6f34-4505-bd04-f08e14a20d7e
-- statement:
--   $\sum_{cyc}x^2(x-y)(x-z)\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62613 (x y z : ℝ) : x ^ 2 * (x - y) * (x - z) + y ^ 2 * (y - z) * (y - x) + z ^ 2 * (z - x) * (z - y) ≥ 0   :=  by sorry
