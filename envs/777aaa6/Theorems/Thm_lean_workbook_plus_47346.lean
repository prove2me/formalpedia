-- Prove2me | Theorems.Thm_lean_workbook_plus_47346
-- name    : lean_workbook_plus_47346
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/bf69bf9c-491b-4902-964d-f2dadf96f54f
-- statement:
--   Given that $a$, $a + 2$, and $a + 4$ are either consecutive even integers or consecutive odd integers, prove that at least one of them is divisible by 3.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47346 (a : ℤ) (h : a % 2 = 0 ∨ a % 2 = 1) : 3 ∣ a ∨ 3 ∣ (a + 2) ∨ 3 ∣ (a + 4)   :=  by sorry
