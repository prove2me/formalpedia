-- Prove2me | Theorems.Thm_lean_workbook_plus_29801
-- name    : lean_workbook_plus_29801
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/7ba802f7-610b-4543-82ed-b3f714bd6edf
-- statement:
--   There are $ 47$ integers between $ 122$ and $ 168$ inclusive.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29801 Finset.card (Finset.filter (λ x => 122<=x ∧ x<=168) (Finset.Icc 1 200)) = 47   :=  by sorry
