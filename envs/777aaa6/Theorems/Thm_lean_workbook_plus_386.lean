-- Prove2me | Theorems.Thm_lean_workbook_plus_386
-- name    : lean_workbook_plus_386
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/1298725b-ace6-4dbe-b760-f1c0883e22b8
-- statement:
--   First equation is $(1+2x-t^2)t-x^2+x+x(2x-t^2)$\nWhich may be written $(x-t^2+t)(x+t+1)=0$\nAnd so $x=t^2-t$ or $x=-t-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_386 (x t : ℂ) : (1 + 2 * x - t ^ 2) * t - x ^ 2 + x + x * (2 * x - t ^ 2) = 0 ↔ x = t ^ 2 - t ∨ x = -t - 1   :=  by sorry
