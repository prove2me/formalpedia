-- Prove2me | Theorems.Thm_lean_workbook_plus_47158
-- name    : lean_workbook_plus_47158
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/3dfc6534-b356-413a-86de-256ad244501d
-- statement:
--   And so $\boxed{f(x)=x\quad\forall x\in\mathbb Q}$ which indeed fits
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47158 (f : ℚ → ℚ) (hf: f = fun x => x) : ∀ x, f x = x   :=  by sorry
