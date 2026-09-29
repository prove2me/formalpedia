-- Prove2me | Theorems.Thm_lean_workbook_plus_57579
-- name    : lean_workbook_plus_57579
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/f5ef74eb-2144-47a3-900e-c4decc2de801
-- statement:
--   WLOG, let $x \le 210 - x$ - in other words, $x$ is the smaller of the two sums, and $210 - x$ is the larger of the two. Then we have $x \le 105$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57579 (x : ℕ) (hx : x ≤ 210 - x) : x ≤ 105   :=  by sorry
