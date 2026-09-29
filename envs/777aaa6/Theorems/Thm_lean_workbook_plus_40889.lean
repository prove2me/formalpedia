-- Prove2me | Theorems.Thm_lean_workbook_plus_40889
-- name    : lean_workbook_plus_40889
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/f942ca74-e5d3-43a1-a789-ef4caac112c5
-- statement:
--   prove: $x-1 \le \lfloor{x \rfloor} \le x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40889 (x : ℝ) : x - 1 ≤ ⌊x⌋ ∧ ⌊x⌋ ≤ x   :=  by sorry
