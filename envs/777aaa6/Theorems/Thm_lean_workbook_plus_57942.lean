-- Prove2me | Theorems.Thm_lean_workbook_plus_57942
-- name    : lean_workbook_plus_57942
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/7c409ac4-33c6-41c9-ba0a-54dba23ebd3e
-- statement:
--   If $ a,b,c,d\ge 0$ and $ a + b + c + d = 4$ then \n $ a\sqrt [3]{b} + b\sqrt [3]{c} + c\sqrt [3]{d} + d\sqrt [3]{a}\le 3 + \sqrt [3]{abcd}.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57942 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hab : a + b + c + d = 4) : a * (b^(1/3)) + b * (c^(1/3)) + c * (d^(1/3)) + d * (a^(1/3)) ≤ 3 + (abcd)^(1/3)   :=  by sorry
