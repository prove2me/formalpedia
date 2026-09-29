-- Prove2me | Theorems.Thm_lean_workbook_plus_43801
-- name    : lean_workbook_plus_43801
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/fafdf499-b911-4862-9825-e145eb1e42c4
-- statement:
--   Prove that,if a and b are nozero integers,then $g.c.d.(a,b)|l.c.m.(a,b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43801 (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : gcd a b ∣ lcm a b   :=  by sorry
