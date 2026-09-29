-- Prove2me | Theorems.Thm_lean_workbook_plus_20659
-- name    : lean_workbook_plus_20659
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d8ba18bc-2a3a-4a99-a92d-8fa5648bc882
-- statement:
--   Then it suffices to show that \n $ \Leftrightarrow a^3 + b^3 + c^3 + 6abc \le 2\left( {ab\left( {a + b} \right) + bc\left( {b + c} \right) + ca\left( {c + a} \right)} \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20659 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a ≥ b) (hbc : b ≥ c) (hca : c ≥ a) : a^3 + b^3 + c^3 + 6 * a * b * c ≤ 2 * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a))   :=  by sorry
