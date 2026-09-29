-- Prove2me | Theorems.Thm_lean_workbook_plus_24396
-- name    : lean_workbook_plus_24396
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/04b05bdb-b85a-4726-a32e-c8a6cd811a15
-- statement:
--   Solve for $x$ in the congruence $4x \equiv 3 \pmod{5}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24396 (x : ℕ) : (4 * x ≡ 3 [ZMOD 5]) ↔ x ≡ 2 [ZMOD 5]   :=  by sorry
