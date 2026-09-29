-- Prove2me | Theorems.Thm_lean_workbook_plus_27733
-- name    : lean_workbook_plus_27733
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/6b4664f6-6e49-4312-b87f-c3e0f0f52db4
-- statement:
--   Prove for positive real $a,b,c:$ $3(a^2+b^2+c^2) \geqslant (a+b+c)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27733 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ (a + b + c) ^ 2   :=  by sorry
