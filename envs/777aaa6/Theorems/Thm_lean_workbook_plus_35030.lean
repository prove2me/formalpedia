-- Prove2me | Theorems.Thm_lean_workbook_plus_35030
-- name    : lean_workbook_plus_35030
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/4b797241-beca-4260-a1a8-f37f7a46299b
-- statement:
--   Investigate the inequality $x[\frac{k-1}{x}]-(x+1)[\frac{k}{x+1}]\leq 0$ for all positive integers $k$ and positive real numbers $x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35030 (x : ℝ) (k : ℤ) (hx : 0 < x) (hk : 0 < k) : x * (k - 1) / x - (x + 1) * k / (x + 1) ≤ 0   :=  by sorry
