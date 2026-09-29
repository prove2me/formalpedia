-- Prove2me | Theorems.Thm_lean_workbook_plus_14191
-- name    : lean_workbook_plus_14191
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/73da6dc3-4f12-4bee-94bf-c7cd0a21b00c
-- statement:
--   If $|x-y|<\epsilon$ for every $\epsilon>0$ , then $x=y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14191 (x y : ℝ) (h : ∀ ε > 0, |x - y| < ε) : x = y   :=  by sorry
