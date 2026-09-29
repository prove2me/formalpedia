-- Prove2me | Theorems.Thm_lean_workbook_plus_6858
-- name    : lean_workbook_plus_6858
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/e3760bfa-3e0b-4bf0-961d-bc59b2714062
-- statement:
--   If $A\leq B,C\leq D$ and $A+C=B+D$ then $A=B$ and $C=D$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6858 {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) (h : a + c = b + d) : a = b ∧ c = d   :=  by sorry
