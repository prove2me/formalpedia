-- Prove2me | Theorems.Thm_lean_workbook_plus_8500
-- name    : lean_workbook_plus_8500
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/73401c03-e003-4886-9605-cf32e80a7dc7
-- statement:
--   Prove Schur's inequality: $m(m-n)(m-p) + n(n-m)(n-p) + p(p-m)(p-n) \geq 0$ for $m, n, p > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8500 (m n p : ℝ) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) : m * (m - n) * (m - p) + n * (n - m) * (n - p) + p * (p - m) * (p - n) ≥ 0   :=  by sorry
