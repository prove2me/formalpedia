-- Prove2me | Theorems.Thm_lean_workbook_plus_63668
-- name    : lean_workbook_plus_63668
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/785c41a7-3b7c-4003-a04b-465c1b417123
-- statement:
--   In $\mathbb{F}_p[x]$, is it true that $x+p-1\mid x^2+p-1$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63668 (p : ℕ) (hp : p.Prime) (F : Type*) [Field F]
  [CharP F p] (x : F) : (x + p - 1) ∣ (x^2 + p - 1)   :=  by sorry
