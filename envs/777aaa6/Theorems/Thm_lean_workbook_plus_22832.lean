-- Prove2me | Theorems.Thm_lean_workbook_plus_22832
-- name    : lean_workbook_plus_22832
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/51cbdde0-4a46-44de-b6c3-e00a24db905a
-- statement:
--   Prove that if $a|b$ , then $2^{a}-1 | 2^{b}-1$ . (What about the converse?)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22832 {a b : ℕ} (h : a ∣ b) : 2 ^ a - 1 ∣ 2 ^ b - 1   :=  by sorry
