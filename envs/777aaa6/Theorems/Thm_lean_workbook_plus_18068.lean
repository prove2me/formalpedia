-- Prove2me | Theorems.Thm_lean_workbook_plus_18068
-- name    : lean_workbook_plus_18068
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/5b742349-73db-4567-a88b-8f6519934828
-- statement:
--   Prove that all nonzero residues modulo a prime $p$ are invertible.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18068 (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) : a * a⁻¹ = 1   :=  by sorry
