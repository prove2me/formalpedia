-- Prove2me | Theorems.Thm_lean_workbook_plus_42229
-- name    : lean_workbook_plus_42229
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/e2eab018-45bd-45c6-9c75-6e8909248e28
-- statement:
--   Prove that $1$ and $p-1$ are the only elements of the field $\mathbb{Z}_p$ that are their own multiplicative inverse.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42229 (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) : a = a⁻¹ ↔ a = 1 ∨ a = p-1   :=  by sorry
