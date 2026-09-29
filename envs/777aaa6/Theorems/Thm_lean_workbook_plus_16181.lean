-- Prove2me | Theorems.Thm_lean_workbook_plus_16181
-- name    : lean_workbook_plus_16181
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/c10ff62b-a626-401a-92b0-dc586c97782d
-- statement:
--   $ x^2+y=a^2+b\implies y-b=(a-x)(a+x)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16181 {x a : ℤ} (h : x^2 + y = a^2 + b) : y - b = (a - x) * (a + x)   :=  by sorry
