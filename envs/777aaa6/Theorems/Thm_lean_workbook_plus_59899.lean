-- Prove2me | Theorems.Thm_lean_workbook_plus_59899
-- name    : lean_workbook_plus_59899
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/5c0937fc-57c9-4b15-80f0-1a035531f086
-- statement:
--   It also follows from the rearrangement inequality: if $a\ge b\ge c$ , then $a^3\ge b^3 \ge c^3$ , so $a^4+b^4+c^4\ge a^3b+b^3c+c^3a$ for all reals $a,b,c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59899 (a b c : ℝ) (hab : a ≥ b) (hbc : b ≥ c) (hca : c ≥ a) : a^4 + b^4 + c^4 ≥ a^3 * b + b^3 * c + c^3 * a   :=  by sorry
