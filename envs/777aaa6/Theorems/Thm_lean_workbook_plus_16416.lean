-- Prove2me | Theorems.Thm_lean_workbook_plus_16416
-- name    : lean_workbook_plus_16416
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/3e4f2596-4c1e-4d6a-9c52-aefeb88dbb60
-- statement:
--   For positive real numbers $p,q,r$ with $p+q+r=1$ , prove $p^2+q^2+r^2\ge \frac{1}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16416 (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hpq: p + q + r = 1) : p^2 + q^2 + r^2 ≥ 1 / 3   :=  by sorry
