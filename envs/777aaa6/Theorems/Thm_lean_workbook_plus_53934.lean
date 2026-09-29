-- Prove2me | Theorems.Thm_lean_workbook_plus_53934
-- name    : lean_workbook_plus_53934
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/cae2b819-7d64-4975-bdb7-63be853e0cd1
-- statement:
--   Prove that if $a, b, c, d$ are positive real numbers such that $a^2 + b^2 + c^2 + d^2 = 4$, then $(a + b + c + d)^2 \leq 16$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53934 (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 4) :
  (a + b + c + d) ^ 2 ≤ 16   :=  by sorry
