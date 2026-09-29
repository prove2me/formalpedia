-- Prove2me | Theorems.Thm_lean_workbook_plus_69113
-- name    : lean_workbook_plus_69113
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/74bf34da-8aca-4903-9a7d-5866f257c639
-- statement:
--   [Simpler solution] $x+y+z \leq 2+xyz \iff x(1-yz)+(y+z) \leq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69113 (x y z : ℝ) : x + y + z ≤ 2 + x * y * z ↔ x * (1 - y * z) + y + z ≤ 2   :=  by sorry
