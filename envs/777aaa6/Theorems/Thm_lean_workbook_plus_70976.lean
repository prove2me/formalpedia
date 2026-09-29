-- Prove2me | Theorems.Thm_lean_workbook_plus_70976
-- name    : lean_workbook_plus_70976
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/eba4ed89-f5a5-4913-8f4f-7432b615eb0b
-- statement:
--   Use part (i) to show that $(p+q+r)^{3} \geq 27pqr$ for any non-negative numbers $p, q$ and $r$ . If $(p+q+r)^{3} = 27pqr$ , what relationship must $p, q$ and $r$ satisfy?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70976 (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) : (p + q + r) ^ 3 ≥ 27 * p * q * r   :=  by sorry
