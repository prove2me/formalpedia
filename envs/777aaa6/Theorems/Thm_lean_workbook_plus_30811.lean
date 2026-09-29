-- Prove2me | Theorems.Thm_lean_workbook_plus_30811
-- name    : lean_workbook_plus_30811
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/77db7629-7c0d-4431-a77d-c2d3785fca49
-- statement:
--   Prove that, for any positive integer $a,b,c,d$, 12 divides $(a-b)(b-c)(c-d)(d-a)(b-d)(a-c)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30811 (a b c d : ℕ) : 12 ∣ (a - b) * (b - c) * (c - d) * (d - a) * (b - d) * (a - c)   :=  by sorry
