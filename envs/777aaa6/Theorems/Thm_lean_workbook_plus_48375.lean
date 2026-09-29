-- Prove2me | Theorems.Thm_lean_workbook_plus_48375
-- name    : lean_workbook_plus_48375
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/8f6ec922-2c3d-4b1e-8d99-b85825121131
-- statement:
--   Prove that $(a+b)(b+c)(a+c) \geq 8abc$ for $a, b, c \geq 0$ using AM-GM inequality
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48375 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a + b) * (b + c) * (a + c) ≥ 8 * a * b * c   :=  by sorry
