-- Prove2me | Theorems.Thm_lean_workbook_plus_29101
-- name    : lean_workbook_plus_29101
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/abba21b2-4a21-4c1e-8555-d98b7dc59496
-- statement:
--   $ \Leftrightarrow \frac {2(ab + bc + ca)}{(a + b)(b + c)(c + a)}\leq \frac {9}{4(a + b + c)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29101 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * (a * b + b * c + c * a)) / (a + b) / (b + c) / (c + a) ≤ 9 / 4 / (a + b + c)   :=  by sorry
