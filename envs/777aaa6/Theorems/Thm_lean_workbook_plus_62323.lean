-- Prove2me | Theorems.Thm_lean_workbook_plus_62323
-- name    : lean_workbook_plus_62323
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/29cdd3a1-278f-4e96-a67b-73d1c293648a
-- statement:
--   f:\mathbb{R} \to \mathbb{R}$ means every $x$ in $\mathbb{R}$ (domain) is assigned a value $f(x)$ which lies in $\mathbb{R}$ (codomain)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62323 (f : ℝ → ℝ) : Set.range f = {y : ℝ | ∃ x : ℝ, y = f x}   :=  by sorry
