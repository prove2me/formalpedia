-- Prove2me | Theorems.Thm_lean_workbook_plus_73696
-- name    : lean_workbook_plus_73696
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/b76a1d08-7328-4e98-95aa-2f336d871616
-- statement:
--   Prove that $ (y - z)(y - x) \leq 0 \Rightarrow y^2 + xz \leq xy + yz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73696 (x y z : ℝ) (h : (y - z) * (y - x) ≤ 0) :
  y^2 + x * z ≤ x * y + y * z   :=  by sorry
