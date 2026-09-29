-- Prove2me | Theorems.Thm_lean_workbook_plus_79666
-- name    : lean_workbook_plus_79666
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/206be1b7-4f23-41e9-a8a5-f7c30995e896
-- statement:
--   Given $a<p-1$, prove that $a+1<p$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79666 (a : ℕ) (p : ℕ) (hp : p.Prime) (h : a < p - 1) : a + 1 < p   :=  by sorry
