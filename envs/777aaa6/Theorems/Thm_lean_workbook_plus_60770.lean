-- Prove2me | Theorems.Thm_lean_workbook_plus_60770
-- name    : lean_workbook_plus_60770
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/57903d10-a90f-4e6e-a3ce-c286b14867f9
-- statement:
--   A simpler example, which takes only rational values and relies on the same idea, is $f(x)=1$ for $x>\sqrt{2}$ and $f(x)=0$ for $x<\sqrt{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60770 : ∃ f : ℚ → ℚ, ∀ x, f x = if x > √2 then 1 else 0   :=  by sorry
