-- Prove2me | Theorems.Thm_lean_workbook_plus_19076
-- name    : lean_workbook_plus_19076
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/49ee04a3-4a52-47a5-be6b-e23fbe3301c4
-- statement:
--   Examples: $a=e$, $b=\ln(2)$, $\Rightarrow$ ${a^b} = {e^{\ln (2)}} = 2 \in \mathbb{Q}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19076 (a b : ℝ) (ha : a = Real.exp 1) (hb : b = Real.log 2) : a^b = 2   :=  by sorry
