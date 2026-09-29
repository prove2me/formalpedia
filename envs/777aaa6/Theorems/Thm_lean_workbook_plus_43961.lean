-- Prove2me | Theorems.Thm_lean_workbook_plus_43961
-- name    : lean_workbook_plus_43961
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/36a99d02-0654-4a0f-a949-09326c9f4250
-- statement:
--   Lemma 1 $a>b>0$ and $c\ge d>0 \implies ac > bd>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43961 (a b c d : ℝ) (h1 : a > b ∧ b > 0) (h2 : c ≥ d ∧ d > 0) : a * c > b * d ∧ b * d > 0   :=  by sorry
