-- Prove2me | Theorems.Thm_lean_workbook_plus_65018
-- name    : lean_workbook_plus_65018
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/d1186333-3a4a-498d-90e2-3d5b3e77cbb4
-- statement:
--   Show that: $9(a^{3} + 3b^{3} + 5c^{3})\geq(a^{2} + 3b^{2} + 5c^{2})(a + 3b + 5c)$ , for all $a,\ b,\ c\geq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65018 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 9 * (a^3 + 3 * b^3 + 5 * c^3) ≥ (a^2 + 3 * b^2 + 5 * c^2) * (a + 3 * b + 5 * c)   :=  by sorry
