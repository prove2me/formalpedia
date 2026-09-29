-- Prove2me | Theorems.Thm_lean_workbook_plus_451
-- name    : lean_workbook_plus_451
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/0f167b83-1397-4820-bbf1-d6e8b394a815
-- statement:
--   Show that: $9(a^{3} + 3b^{3} + 5c^{3})\geq(a^{2} + 3b^{2} + 5c^{2})(a + 3b + 5c)$ , for all $a,\ b,\ c\geq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_451 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 9 * (a^3 + 3 * b^3 + 5 * c^3) ≥ (a^2 + 3 * b^2 + 5 * c^2) * (a + 3 * b + 5 * c)   :=  by sorry
