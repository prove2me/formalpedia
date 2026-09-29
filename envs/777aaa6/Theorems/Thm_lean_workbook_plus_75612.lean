-- Prove2me | Theorems.Thm_lean_workbook_plus_75612
-- name    : lean_workbook_plus_75612
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/18769382-9c2a-4888-ad46-e19282310305
-- statement:
--   to repeat a three digit number we multiply it by 1000 and add the number (1000N+N) so we get 1001 N $\boxed{E}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75612 (N : ℕ) (hN : 1 ≤ N ∧ N ≤ 999) : 1001 * N = 1000 * N + N   :=  by sorry
