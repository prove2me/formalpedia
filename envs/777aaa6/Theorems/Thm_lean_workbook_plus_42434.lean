-- Prove2me | Theorems.Thm_lean_workbook_plus_42434
-- name    : lean_workbook_plus_42434
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/45ddd737-132c-41a4-a782-bded18db2443
-- statement:
--   If $a, b,\text{ and } c$ are nonzero numbers satisfying $3a = 4b$ and $5b = 6c$ , what is $\frac{c}{a+b}$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42434 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : 3*a = 4*b) (hbc : 5*b = 6*c) : c/(a+b) = 5/14   :=  by sorry
