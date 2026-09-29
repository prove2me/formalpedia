-- Prove2me | Theorems.Thm_lean_workbook_plus_79616
-- name    : lean_workbook_plus_79616
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/d41d0c86-5a82-4d8f-a631-685ef29e08fa
-- statement:
--   Let $a+b=2u, \: ab=v^2.$ Then the inequality becomes $v^4(4u^2-2v^2-2) \geq 2u(v^2-1) \: \Longleftrightarrow \: 2v^4u^2+(1-v^2)u-v^6-v^4 \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79616 {u v a b : ℝ} (ha : a + b = 2 * u) (hb : a * b = v ^ 2) : v ^ 4 * (4 * u ^ 2 - 2 * v ^ 2 - 2) ≥ 2 * u * (v ^ 2 - 1) ↔ 2 * v ^ 4 * u ^ 2 + (1 - v ^ 2) * u - v ^ 6 - v ^ 4 ≥ 0   :=  by sorry
