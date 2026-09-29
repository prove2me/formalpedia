-- Prove2me | Theorems.Thm_lean_workbook_plus_40167
-- name    : lean_workbook_plus_40167
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/2714dfe8-8a18-495a-a3e3-4b6667faccad
-- statement:
--   Prove that \((a^2 + b^2)^2 \geq (a + b + c)(a + b - c)(b + c - a)(c + a - b)\) using the inequality \(xy \leq \frac{(x+y)^2}{4}\) for all \(x, y \in \mathbb{R}\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40167 (a b c : ℝ) : (a^2 + b^2)^2 ≥ (a + b + c) * (a + b - c) * (b + c - a) * (c + a - b)   :=  by sorry
