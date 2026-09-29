-- Prove2me | Theorems.Thm_lean_workbook_plus_34471
-- name    : lean_workbook_plus_34471
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/4f18b115-bea4-49a0-9086-5559f6cf58f7
-- statement:
--   If $a_k\ge 0$ and $\sum a_k$ converges, then $\sum {a_k\over 1+ka_k}$ converges
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34471 (a : ℕ → NNReal) (h : Summable a) : Summable (fun k ↦ a k / (1 + k * a k))   :=  by sorry
