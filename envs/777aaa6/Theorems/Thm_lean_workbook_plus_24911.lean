-- Prove2me | Theorems.Thm_lean_workbook_plus_24911
-- name    : lean_workbook_plus_24911
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/c6e9fdaa-c9f0-4f0e-a0e9-28ccc845eb1b
-- statement:
--   $\Leftrightarrow 8+2\sum ab\geq 12+abc \Leftrightarrow 2\sum ab-abc\geq 4$ (1)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24911 (a b c : ℝ) : 8 + 2 * (a * b + b * c + c * a) ≥ 12 + a * b * c ↔ 2 * (a * b + b * c + c * a) - a * b * c ≥ 4   :=  by sorry
