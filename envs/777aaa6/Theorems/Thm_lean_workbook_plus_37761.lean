-- Prove2me | Theorems.Thm_lean_workbook_plus_37761
-- name    : lean_workbook_plus_37761
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/d4da16c5-4fb2-4088-81c2-2006a38ba3d6
-- statement:
--   Let $g:\mathbb{Z}\to\mathbb{Z}$ be defined as $f(x)-x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37761 (x : ℤ) (f : ℤ → ℤ) (g : ℤ → ℤ) (h₁ : g = f - x) : g x = f x - x   :=  by sorry
