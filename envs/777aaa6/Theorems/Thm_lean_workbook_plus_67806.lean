-- Prove2me | Theorems.Thm_lean_workbook_plus_67806
-- name    : lean_workbook_plus_67806
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/a4495cf3-8315-4912-a714-9b8f72005d05
-- statement:
--   A number $\overline{abcd}$ is divisible by 8 iff $\overline{bcd}$ is divisible by 8.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67806 : ∀ a b c d : ℕ, a * 10 ^ 3 + b * 10 ^ 2 + c * 10 + d ≡ 0 [ZMOD 8] ↔ b * 10 ^ 2 + c * 10 + d ≡ 0 [ZMOD 8]   :=  by sorry
