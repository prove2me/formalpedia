-- Prove2me | Theorems.Thm_lean_workbook_plus_16703
-- name    : lean_workbook_plus_16703
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/0a0d6d11-938b-46d9-86aa-a51d9e759fff
-- statement:
--   (By Cauchy-Schwarz) $(asiny+bcosz+c)^2\leq(a^2+b^2+c^2)(sin^2y+cos^2z+1^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16703 {a b c : ℝ} {y z : ℝ} : (a * sin y + b * cos z + c) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (sin y ^ 2 + cos z ^ 2 + 1 ^ 2)   :=  by sorry
