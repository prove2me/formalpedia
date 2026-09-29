-- Prove2me | Theorems.Thm_lean_workbook_plus_34388
-- name    : lean_workbook_plus_34388
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/e5a5b7e1-a6f9-42d7-9441-f7fcd5af0c77
-- statement:
--   If $n = 74892^{359}$ x $6379^{207}$ x $9538^{179}$ x $3756^{723}$ find the remainder when n is divided by 5.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34388 (n : ℕ) : n = 74892^359 * 6379^207 * 9538^179 * 3756^723 → n % 5 = 4   :=  by sorry
