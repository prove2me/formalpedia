-- Prove2me | Theorems.Thm_lean_workbook_plus_58551
-- name    : lean_workbook_plus_58551
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/4b0061cd-3229-4717-86eb-d55c3105413c
-- statement:
--   Prove the lemma: For positive $a, b, c, d$, if $\frac{a}{b}>\frac{c}{d}$, then $\frac{a}{b}>\frac{a+c}{b+d}>\frac{c}{d}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58551 (a b c d : ℝ) (h1 : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) (h2 : a / b > c / d) : a / b > (a + c) / (b + d) ∧ (a + c) / (b + d) > c / d   :=  by sorry
