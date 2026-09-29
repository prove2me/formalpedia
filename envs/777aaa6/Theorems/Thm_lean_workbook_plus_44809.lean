-- Prove2me | Theorems.Thm_lean_workbook_plus_44809
-- name    : lean_workbook_plus_44809
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/f049d067-b2de-4647-9066-0e99ff0199b6
-- statement:
--   Prove that $a^2+ac+c^2\ge 3b(a-b+c)$ given $a,b,c\in R; \ \ \ a\ge b\ge c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44809 (a b c : ℝ) (hab : a ≥ b) (hbc : b ≥ c) : a^2 + a*c + c^2 ≥ 3*b*(a - b + c)   :=  by sorry
