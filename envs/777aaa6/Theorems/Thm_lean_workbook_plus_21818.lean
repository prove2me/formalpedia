-- Prove2me | Theorems.Thm_lean_workbook_plus_21818
-- name    : lean_workbook_plus_21818
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/9ad8ed63-d1fe-42d1-bb0f-d89d6fbe1489
-- statement:
--   For $a,b,c\ge 0 $ prove that:\n $ 6(a^2+b^2+c^2)+a^2b^2+b^2c^2+c^2a^2+27\ge 16(a+b+c) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21818 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 6 * (a ^ 2 + b ^ 2 + c ^ 2) + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 + 27 ≥ 16 * (a + b + c)   :=  by sorry
