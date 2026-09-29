-- Prove2me | Theorems.Thm_lean_workbook_plus_31027
-- name    : lean_workbook_plus_31027
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/db12b9b6-3af0-48c6-91ef-5541f01b3cf2
-- statement:
--   3. $Q(c,0): 3f(0)+3c=0 \implies f(0)=-c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31027 {f : ℝ → ℝ} (c : ℝ) (h : 3 * f 0 + 3 * c = 0) : f 0 = -c   :=  by sorry
