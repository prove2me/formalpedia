-- Prove2me | Theorems.Thm_lean_workbook_plus_66652
-- name    : lean_workbook_plus_66652
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/8bf9b41c-41bd-4214-8642-d9dc6a25263b
-- statement:
--   Let $a$ , $b$ and $c$ be non-negative numbers. Prove that: $a^3+b^3-3ab+1\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66652 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^3 + b^3 - 3 * a * b + 1 ≥ 0   :=  by sorry
