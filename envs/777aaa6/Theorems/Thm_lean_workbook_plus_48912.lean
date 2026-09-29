-- Prove2me | Theorems.Thm_lean_workbook_plus_48912
-- name    : lean_workbook_plus_48912
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5c25e7d3-77cb-4a0f-a15b-2d0850cb2ef2
-- statement:
--   Derive the factorization $r^3 + s^3 + t^3 - 3rst = (r + s + t)((r + s + t)^2 - 3(rs + st + rt))$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48912 (r s t : ℝ) :
  r^3 + s^3 + t^3 - 3 * r * s * t =
    (r + s + t) * ((r + s + t)^2 - 3 * (r * s + s * t + r * t))   :=  by sorry
