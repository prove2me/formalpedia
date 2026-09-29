-- Prove2me | Theorems.Thm_lean_workbook_plus_4816
-- name    : lean_workbook_plus_4816
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/245aa7ed-11d6-48b1-9f72-28996e2bc4d7
-- statement:
--   Prove that if $a$ and $b$ are integers that leave the same remainder when divided by 8, then $a^2$ and $b^2$ also leave the same remainder when divided by 8.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4816 {a b : ℤ} (h : a % 8 = b % 8) : a^2 % 8 = b^2 % 8   :=  by sorry
