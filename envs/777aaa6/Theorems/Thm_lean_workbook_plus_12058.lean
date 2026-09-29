-- Prove2me | Theorems.Thm_lean_workbook_plus_12058
-- name    : lean_workbook_plus_12058
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/8264dc90-2144-4af0-957d-4de314b44030
-- statement:
--   Given any function $f$ , the unique decomposition into even and odd parts is $f(x)=\left(\frac12f(x)+\frac12f(-x)\right)+\left(\frac12f(x)-\frac12f(-x)\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12058 (f : ℝ → ℝ) : ∀ x, f x = (f x + f (-x)) / 2 + (f x - f (-x)) / 2   :=  by sorry
