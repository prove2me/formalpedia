-- Prove2me | Theorems.Thm_lean_workbook_plus_23477
-- name    : lean_workbook_plus_23477
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/2bb7d74b-0951-4019-91ec-a6f34aed69e8
-- statement:
--   Then $N = 13^2 + 14^2 + 15^2 + \ldots + 30^2 = \dfrac{30 \cdot 31 \cdot 61 - 12 \cdot 13 \cdot 25}{6} = 8805$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23477 :
  ∑ k in (Finset.Icc 13 30), k^2 = 8805   :=  by sorry
