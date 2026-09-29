-- Prove2me | Theorems.Thm_lean_workbook_plus_2284
-- name    : lean_workbook_plus_2284
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/08ca2653-c8f1-4c77-9ce0-09ab6feca9f2
-- statement:
--   Prove $ f(x)=0$ $ \iff$ $ x=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2284 (f : ℝ → ℝ) (hf: f x = 0) (hx: x = 0) : f x = 0 ↔ x = 0   :=  by sorry
