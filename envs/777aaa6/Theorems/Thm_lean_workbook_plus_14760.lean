-- Prove2me | Theorems.Thm_lean_workbook_plus_14760
-- name    : lean_workbook_plus_14760
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/8cf63902-792e-4156-b0ee-c7719cb8a551
-- statement:
--   with $f(u)=u-1-\ln u$ , show that $0<u\neq 1\Rightarrow~f(u)>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14760 (u : ℝ) (h : 0 < u) (h' : u ≠ 1) : u - 1 - Real.log u > 0   :=  by sorry
