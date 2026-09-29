-- Prove2me | Theorems.Thm_lean_workbook_plus_17268
-- name    : lean_workbook_plus_17268
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/8eaf5467-6d49-4dcb-85b7-97e4c3dd9c3b
-- statement:
--   (1) $\log_n m < \lfloor \log_n mn \rfloor$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17268 (n m : ℕ) (hn : 1 < n) (hm : 1 < m) : Real.logb n m < ⌊Real.logb n (m * n)⌋   :=  by sorry
