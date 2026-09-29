-- Prove2me | Theorems.Thm_lean_workbook_plus_42220
-- name    : lean_workbook_plus_42220
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/e93cd394-1fbd-4800-be2b-adcaac75a45b
-- statement:
--   $(a-b)(b-c)(c-a)=0\Longrightarrow a=b$ or $b=c$ or $c=a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42220 {a b c : ℂ} (h : (a - b) * (b - c) * (c - a) = 0) :
  a = b ∨ b = c ∨ c = a   :=  by sorry
