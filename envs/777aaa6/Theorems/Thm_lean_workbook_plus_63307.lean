-- Prove2me | Theorems.Thm_lean_workbook_plus_63307
-- name    : lean_workbook_plus_63307
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/913f6ef5-2f3c-4064-818e-33590bb2c7c3
-- statement:
--   If $f(x) = \lfloor x \rfloor +1$ then $f(f(x)) = f( \lfloor x \rfloor +1 ) = \lfloor \lfloor x \rfloor +1 \rfloor + 1 = \lfloor x \rfloor + 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63307  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = Int.floor x + 1) :
  ∀ x, f (f x) = Int.floor x + 2   :=  by sorry
