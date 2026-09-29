-- Prove2me | Theorems.Thm_lean_workbook_plus_76221
-- name    : lean_workbook_plus_76221
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/a4f3c9ab-87e3-4523-9661-ea693023fb9c
-- statement:
--   Each match, 5 players get eliminated. We need 215 players to get eliminated to have a victor. Hence, there must be $215/5=43$ matches.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76221  (n : ℕ)
  (h₀ : 5 * n = 215) :
  n = 43   :=  by sorry
