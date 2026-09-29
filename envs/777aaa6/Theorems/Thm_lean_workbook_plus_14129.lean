-- Prove2me | Theorems.Thm_lean_workbook_plus_14129
-- name    : lean_workbook_plus_14129
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/28a2d7c7-3eb5-45fd-920d-004a14534470
-- statement:
--   Prove the statement $F_k+F_{k+1}=F_{k+2}$ for nonnegative $k$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14129 : ∀ k : ℕ, fib k + fib (k + 1) = fib (k + 2)   :=  by sorry
