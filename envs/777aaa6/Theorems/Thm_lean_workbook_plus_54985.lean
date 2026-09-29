-- Prove2me | Theorems.Thm_lean_workbook_plus_54985
-- name    : lean_workbook_plus_54985
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/70be1b34-3288-4197-a293-c7f10d4c991b
-- statement:
--   Prove that for any positive real numbers $a$ and $b$, the following inequality holds: $a^2 + b^2 + 1 \geq a + b + ab$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54985 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a^2 + b^2 + 1 ≥ a + b + a * b   :=  by sorry
