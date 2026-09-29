-- Prove2me | Theorems.Thm_lean_workbook_plus_18523
-- name    : lean_workbook_plus_18523
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/6ee00540-6090-4584-b494-5e21795084dc
-- statement:
--   Let G be a group of order n (i.e $ |G| = n$ ). Show: $ n = \Sigma_{m|n} \varphi(m)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18523 (G : Type*) [Fintype G] : Fintype.card G = ∑ m in divisors (Fintype.card G), φ m   :=  by sorry
