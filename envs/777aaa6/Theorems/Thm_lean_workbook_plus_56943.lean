-- Prove2me | Theorems.Thm_lean_workbook_plus_56943
-- name    : lean_workbook_plus_56943
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/e0fdb6e4-a531-478b-9020-61b343118f9b
-- statement:
--   $P(0,0)$ $\implies$ $f(0)\in\{0,1\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56943 (f : ℕ → ℕ) (hf: f 0 = 0 ∨ f 0 = 1) : ∃ (a : ℕ), a = 0 ∨ a = 1   :=  by sorry
