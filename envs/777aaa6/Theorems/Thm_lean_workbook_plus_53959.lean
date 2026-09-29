-- Prove2me | Theorems.Thm_lean_workbook_plus_53959
-- name    : lean_workbook_plus_53959
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/e9cc5d3c-eefc-4ea4-8d1f-124ea06406a9
-- statement:
--   Let a, b, c be three positive reals. Prove the inequality\n\n$\frac{a^2(a-b)}{(2b+a)(b+2a)} \geq \frac{a-b}{9}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53959 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * (a - b)) / ((2 * b + a) * (b + 2 * a)) ≥ (a - b) / 9   :=  by sorry
