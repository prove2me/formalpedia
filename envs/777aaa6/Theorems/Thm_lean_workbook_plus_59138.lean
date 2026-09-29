-- Prove2me | Theorems.Thm_lean_workbook_plus_59138
-- name    : lean_workbook_plus_59138
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/042bfc78-1e6a-4d20-9a56-2b972ace1e18
-- statement:
--   Prove the identity\n\n\( \frac{a^5+b^5+c^5}{5}=(\frac{a^2+b^2+c^2}{2})(\frac{a^3+b^3+c^3}{3}) \)\n\nGiven: \( a+b+c=0 \)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59138 {a b c : ℝ} (h : a + b + c = 0) :
  (a^5 + b^5 + c^5) / 5 = (a^2 + b^2 + c^2) / 2 * (a^3 + b^3 + c^3) / 3   :=  by sorry
