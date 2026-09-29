-- Prove2me | Theorems.Thm_lean_workbook_plus_15131
-- name    : lean_workbook_plus_15131
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/c6d41bf9-02cf-4101-ab0c-5a0950358a0c
-- statement:
--   Prove that ${n \choose k} + {n \choose k + 1} = {n + 1 \choose k + 1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15131 (n k : ℕ) : choose n k + choose n (k + 1) = choose (n + 1) (k + 1)   :=  by sorry
