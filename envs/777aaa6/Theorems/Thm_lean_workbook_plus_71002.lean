-- Prove2me | Theorems.Thm_lean_workbook_plus_71002
-- name    : lean_workbook_plus_71002
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/6c4d916f-005a-4c9d-8bd4-4455e302edcb
-- statement:
--   Prove that if $t$ divides $(t+3)^2 - 3$, then $t$ divides $3^3 - 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71002 (t : ℕ) (h : t ∣ (t + 3)^2 - 3) : t ∣ 3^3 - 3   :=  by sorry
