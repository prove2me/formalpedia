-- Prove2me | Theorems.Thm_lean_workbook_plus_49637
-- name    : lean_workbook_plus_49637
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b684e4b1-b855-4c18-9264-562e7f752008
-- statement:
--   Because f is strictly increasing, then $f(n) \geq n, \forall n\in \mathbb{N}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49637 (f : ℕ → ℕ) (hf: StrictMono f) : ∀ n, f n ≥ n   :=  by sorry
