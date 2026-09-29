-- Prove2me | Theorems.Thm_lean_workbook_plus_64253
-- name    : lean_workbook_plus_64253
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/0aec9fe0-0706-4c44-9904-2193e9c8a9a2
-- statement:
--   That's simple. Note that every product can be written as $ 8n^3 $ . So the sum is actually $ 8 \sum_{n=1}^{10}n^3 $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64253 :
  ∑ k in (Finset.Icc 1 10), (2 * (k + 1) * (k + 2)) = 8 * ∑ k in (Finset.Icc 1 10), k^3   :=  by sorry
