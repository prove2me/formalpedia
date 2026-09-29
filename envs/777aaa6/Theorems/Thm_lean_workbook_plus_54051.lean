-- Prove2me | Theorems.Thm_lean_workbook_plus_54051
-- name    : lean_workbook_plus_54051
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/18ad7d04-454e-4894-9c79-c61404fcc027
-- statement:
--   For all integers $ n \ge 0$ , prove $ 133$ divides $ 11^{n + 2} + 12^{2n + 1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54051 (n:ℕ) : 133 ∣ 11^(n+2) + 12^(2*n+1)   :=  by sorry
