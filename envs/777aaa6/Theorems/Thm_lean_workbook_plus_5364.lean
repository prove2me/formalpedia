-- Prove2me | Theorems.Thm_lean_workbook_plus_5364
-- name    : lean_workbook_plus_5364
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/b6d71074-1ff9-4a96-a37f-91baf8d27982
-- statement:
--   Show that any infinite subset of $\mathbb{N}$ can be bijectively mapped to $\mathbb{N}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5364 (s : Set ℕ) (h : s.Infinite) :
    ∃ f : ℕ → ℕ, Function.Bijective f   :=  by sorry
