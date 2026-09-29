-- Prove2me | Theorems.Thm_lean_workbook_plus_24143
-- name    : lean_workbook_plus_24143
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/673521e1-de1f-4430-b1d1-51d1b510e8f2
-- statement:
--   Prove that $ \lvert{a + b - c}\rvert + \lvert{b + c - a}\rvert + \lvert {c + a - b}\rvert \ge \lvert {a - b}\rvert + \lvert{b - c}\rvert + \lvert{c - a}\rvert$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24143 (a b c : ℝ) : 
  |a + b - c| + |b + c - a| + |c + a - b| ≥ |a - b| + |b - c| + |c - a|   :=  by sorry
