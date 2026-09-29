-- Prove2me | Theorems.Thm_lean_workbook_plus_65403
-- name    : lean_workbook_plus_65403
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c8e4a013-71a9-4bf8-8b85-feb1ff1017dc
-- statement:
--   Prove that if $ x $ and $ y $ are positive integers where $ x>1 $ , then $ x^y-1 $ is divisible by $ x-1 $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65403 (x y : ℕ) (hx : 1 < x) : (x - 1) ∣ (x^y - 1)   :=  by sorry
