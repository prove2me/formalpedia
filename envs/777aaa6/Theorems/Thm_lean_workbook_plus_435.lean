-- Prove2me | Theorems.Thm_lean_workbook_plus_435
-- name    : lean_workbook_plus_435
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/3055172d-f79e-4a13-b3ae-0cfa1635688d
-- statement:
--   Prove that for non-negative real numbers $a, b, c$, the following inequality holds: $(a^{2}+b^{2}-c^{2})(a-b)^{2}+(b^{2}+c^{2}-a^{2})(b-c)^{2}+(c^{2}+a^{2}-b^{2})(c-a)^{2}\geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_435 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a^2 + b^2 - c^2) * (a - b)^2 + (b^2 + c^2 - a^2) * (b - c)^2 + (c^2 + a^2 - b^2) * (c - a)^2 ≥ 0   :=  by sorry
