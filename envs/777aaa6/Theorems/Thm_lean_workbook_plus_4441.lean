-- Prove2me | Theorems.Thm_lean_workbook_plus_4441
-- name    : lean_workbook_plus_4441
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/71b6b124-63bf-4ea7-8408-ab3a6b042e29
-- statement:
--   Prove that for any four real numbers $a$ , $b$ , $c$ , $d$ , the inequality \n $ \left(a-b\right)\left(b-c\right)\left(c-d\right)\left(d-a\right)+\left(a-c\right)^2\left(b-d\right)^2\geq 0 $ \n holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4441 (a b c d : ℝ) :  (a - b) * (b - c) * (c - d) * (d - a) + (a - c) ^ 2 * (b - d) ^ 2 ≥ 0   :=  by sorry
