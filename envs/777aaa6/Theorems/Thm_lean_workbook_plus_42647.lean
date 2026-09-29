-- Prove2me | Theorems.Thm_lean_workbook_plus_42647
-- name    : lean_workbook_plus_42647
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/09a46dfd-0b85-461a-8f09-007e21fe35a4
-- statement:
--   If $x<0$ , then $|x|=-x$ ; if also $x+k<0$ , then we get $|x+k|=-x-k\ne -x+k$ since $k\ne0$ ; if instead $x+k\ge0$ , then $|x+k|=x+k\ne -x+k$ since $x\ne0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42647  (x k : ℝ)
  (h₀ : x < 0)
  (h₁ : x + k < 0)
  (h₂ : k ≠ 0) :
  |x + k| ≠ -x + k   :=  by sorry
