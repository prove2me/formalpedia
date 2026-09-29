-- Prove2me | Theorems.Thm_lean_workbook_plus_76080
-- name    : lean_workbook_plus_76080
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e40654a0-55fb-455c-a590-1365d4a08ddd
-- statement:
--   $(a - b)^4 + (b - c)^4 + (c - a)^4 \ge 0$ ? Or more generally $(a - b)^{2n} + (b - c)^{2n} + (c - a)^{2n} \ge 0$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76080 (a b c : ℝ) (n : ℕ) : (a - b) ^ (2 * n) + (b - c) ^ (2 * n) + (c - a) ^ (2 * n) ≥ 0   :=  by sorry
