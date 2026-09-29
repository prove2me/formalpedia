-- Prove2me | Theorems.Thm_lean_workbook_plus_59982
-- name    : lean_workbook_plus_59982
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e6f0e6b3-c3ca-487b-838f-ea57143b672e
-- statement:
--   What is $(2000 + 2001 + 2002 + ... + 2099) - (1900 + 1901 + 1902 + ...+ 1999)$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59982 (n : ℕ) : (∑ k in Finset.Icc 2000 2099, k) - (∑ k in Finset.Icc 1900 1999, k) = 5000   :=  by sorry
