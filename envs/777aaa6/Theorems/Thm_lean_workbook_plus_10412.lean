-- Prove2me | Theorems.Thm_lean_workbook_plus_10412
-- name    : lean_workbook_plus_10412
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/0c335494-0af8-4650-b989-4cf848994564
-- statement:
--   Observe that $2^{k-1}\geq k, \forall k\in \mathbb{Z^+}$ (an easy practice on induction).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10412 (k : ℕ) (h : 1 ≤ k) : 2 ^ (k - 1) ≥ k   :=  by sorry
