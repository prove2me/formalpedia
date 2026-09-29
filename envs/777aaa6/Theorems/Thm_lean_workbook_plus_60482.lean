-- Prove2me | Theorems.Thm_lean_workbook_plus_60482
-- name    : lean_workbook_plus_60482
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/d364e3bb-46ca-41f5-9240-8ab9919813cb
-- statement:
--   Let $ a,b $ two elements of a group. If $ a $ has order $ n>1 $ and $ a^{n-1}b=ab^{n-1} $ prove that $ ab=ba $.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60482  {G : Type*} [Group G] {a b : G} {n : ℕ} (h : 1 < n) (h' : a ^ n = 1) (h'' : a ^ (n - 1) * b = b * a ^ (n - 1)) :
  a * b = b * a   :=  by sorry
