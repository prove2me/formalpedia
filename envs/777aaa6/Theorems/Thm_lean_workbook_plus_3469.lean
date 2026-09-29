-- Prove2me | Theorems.Thm_lean_workbook_plus_3469
-- name    : lean_workbook_plus_3469
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/89edb9e7-3161-4e07-b0a1-48ab842cb759
-- statement:
--   Prove that $(3a+b)(3b+a) \ge 2(a+b)(\sqrt{a}+\sqrt{b})^2$ for non-negative numbers $a$ and $b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3469 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (3 * a + b) * (3 * b + a) ≥ 2 * (a + b) * (Real.sqrt a + Real.sqrt b) ^ 2   :=  by sorry
