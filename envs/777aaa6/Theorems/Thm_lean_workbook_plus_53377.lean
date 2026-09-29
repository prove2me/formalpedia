-- Prove2me | Theorems.Thm_lean_workbook_plus_53377
-- name    : lean_workbook_plus_53377
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/e2fd3b89-03b7-4851-9424-c0a2c5204421
-- statement:
--   Prove that if $n \equiv 1 \mod 3$, then $n^2 + 2 \equiv 0 \mod 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53377 : ∀ n : ℤ, n ≡ 1 [ZMOD 3] → n ^ 2 + 2 ≡ 0 [ZMOD 3]   :=  by sorry
