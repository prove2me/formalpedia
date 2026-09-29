-- Prove2me | Theorems.Thm_lean_workbook_plus_9918
-- name    : lean_workbook_plus_9918
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/1ef94347-c2f9-4207-92f2-f14cd8151a45
-- statement:
--   Prove the rule: $\frac{x}{y}<\frac{x+a}{y+a}$ where $a>0, x>0, y>0$ and $x<y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9918 (x y a : ℝ) (ha : 0 < a) (hx : 0 < x) (hy : 0 < y) (hxy : x < y) : x / y < (x + a) / (y + a)   :=  by sorry
