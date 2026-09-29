-- Prove2me | Theorems.Thm_lean_workbook_plus_44974
-- name    : lean_workbook_plus_44974
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/45abf808-3097-462a-ad7c-105ccc76a807
-- statement:
--   Prove that \(n+\frac{1}{2}<\sqrt{n^2+n+1}<n+1\) for all positive integers n.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44974 (n : ℕ) (hn : n > 0) : (n + 1/2) < Real.sqrt (n^2 + n + 1) ∧ Real.sqrt (n^2 + n + 1) < n + 1   :=  by sorry
