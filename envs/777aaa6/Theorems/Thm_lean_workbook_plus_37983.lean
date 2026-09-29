-- Prove2me | Theorems.Thm_lean_workbook_plus_37983
-- name    : lean_workbook_plus_37983
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/bcde6aa7-cc6a-4aaf-a2e0-f94560cfe201
-- statement:
--   By CS: \n $\sum\frac{a+2c}{a+b}=\sum\frac{(a+2c)^2}{(a+2c)(a+b)}\ge \frac{9\sum a^2+18\sum ab}{\sum a^2+5\sum ab}\ge \frac{9}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37983 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 2 * c) / (a + b) + (b + 2 * a) / (b + c) + (c + 2 * b) / (c + a) ≥ 9 / 2   :=  by sorry
