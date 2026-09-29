-- Prove2me | Theorems.Thm_lean_workbook_plus_70637
-- name    : lean_workbook_plus_70637
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/f899cba0-7a21-41c4-9172-5f9ee9ebef4d
-- statement:
--   Actually, for all even $z$ it holds that $z^2 \equiv 0\mod4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70637 {z : ℤ} (h : z % 2 = 0) : z ^ 2 ≡ 0 [ZMOD 4]   :=  by sorry
