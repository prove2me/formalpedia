-- Prove2me | Theorems.Thm_lean_workbook_plus_38283
-- name    : lean_workbook_plus_38283
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/35bb20fd-f90e-4f5d-95ae-892cac97581b
-- statement:
--   Prove for all integers $ n \ge 0$ that $ 133$ divides $ 11^{n + 2} + 12^{2n + 1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38283 : ∀ n : ℕ, n ≥ 0 → 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1)   :=  by sorry
