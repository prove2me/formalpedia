-- Prove2me | Theorems.Thm_lean_workbook_plus_4857
-- name    : lean_workbook_plus_4857
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/73c538f6-f210-4c34-917a-310898fb8d5c
-- statement:
--   Prove that if $a+b+c=3$ , then $ab+bc+ac<=3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4857 (a b c : ℝ) (ha : a + b + c = 3) : a * b + b * c + c * a <= 3   :=  by sorry
