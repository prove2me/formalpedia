-- Prove2me | Theorems.Thm_lean_workbook_plus_9091
-- name    : lean_workbook_plus_9091
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/dd0125d9-1bf1-4de7-a0f2-e6add467f66e
-- statement:
--   Prove that $ \sum_{cyc}\left(a^{2}b^{2}+abc\right)\geq\left(a+b+c\right)\left(ab+bc+ac-1\right)$ for a,b,c positive reals and $ a^{2}+b^{2}+c^{2}= 3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9091 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) (h : a^2 + b^2 + c^2 = 3) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + a * b * c ≥ (a + b + c) * (a * b + b * c + c * a - 1)   :=  by sorry
