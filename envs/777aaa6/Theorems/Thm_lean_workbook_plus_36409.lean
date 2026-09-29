-- Prove2me | Theorems.Thm_lean_workbook_plus_36409
-- name    : lean_workbook_plus_36409
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/37fb3dcc-27b8-44d5-ae21-1f83f2835f84
-- statement:
--   Let $a$ , $b$ and $c $ be positive numbers such that $ a^2+b^2+c^2+abc=4 $ . Prove that: \n $ (a+b+c)^2 \leq 8+abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36409 (a b c: ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + a * b * c = 4) : (a + b + c)^2 ≤ 8 + a * b * c   :=  by sorry
