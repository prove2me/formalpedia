-- Prove2me | Theorems.Thm_lean_workbook_plus_48076
-- name    : lean_workbook_plus_48076
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/020ecab8-d15e-4d1d-bf6d-63ad5e3cd1cb
-- statement:
--   Prove that: $48a^2 + 12b^2 + 255 \geq 104a + 101a + 20ab$ given $a \geq 3$, $b \geq 3$, and $a^2 \geq 3b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48076 (a b : ℝ) (ha : 3 ≤ a) (hb : 3 ≤ b) (h : a^2 ≥ 3 * b) : 48 * a^2 + 12 * b^2 + 255 ≥ 104 * a + 101 * a + 20 * a * b   :=  by sorry
