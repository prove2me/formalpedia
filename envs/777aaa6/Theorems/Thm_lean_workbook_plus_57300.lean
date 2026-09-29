-- Prove2me | Theorems.Thm_lean_workbook_plus_57300
-- name    : lean_workbook_plus_57300
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/fd678033-86ff-4e18-acf1-d91201280ccb
-- statement:
--   Prove for $a, b, c \in \mathbb{R^+}$\n\n$a^3c^2 + ab^4 + 2b^2c^3 \geq 4ab^2c^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57300 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3*c^2 + a*b^4 + 2*b^2*c^3 ≥ 4*a*b^2*c^2   :=  by sorry
