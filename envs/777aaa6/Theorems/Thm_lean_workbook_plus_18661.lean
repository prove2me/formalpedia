-- Prove2me | Theorems.Thm_lean_workbook_plus_18661
-- name    : lean_workbook_plus_18661
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d4640027-e9bd-47ec-bebb-18f9a5dfe3a8
-- statement:
--   prove that $ \left|a \right|+\left|b \right|+\left|c \right|+\left|a+b+c \right|\geq\left|a+b \right|+\left|b+c \right|+\left|a+c \right|$, for all real numbers $a, b, c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18661 (a b c: ℝ) : abs a + abs b + abs c + abs (a + b + c) ≥ abs (a + b) + abs (b + c) + abs (a + c)   :=  by sorry
