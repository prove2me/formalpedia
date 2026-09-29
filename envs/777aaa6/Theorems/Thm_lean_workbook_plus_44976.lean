-- Prove2me | Theorems.Thm_lean_workbook_plus_44976
-- name    : lean_workbook_plus_44976
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/13d82b1e-dc57-461c-9c61-f3d85cab1cfc
-- statement:
--   Prove that $a\sqrt{bc}\le \sqrt{abc}$ given $a\le 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44976 (a b c : ℝ) (ha : 0 < a ∧ a ≤ 1) (hb : 0 < b) (hc : 0 < c) : a * Real.sqrt (b * c) ≤ Real.sqrt (a * b * c)   :=  by sorry
