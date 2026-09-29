-- Prove2me | Theorems.Thm_lean_workbook_plus_15286
-- name    : lean_workbook_plus_15286
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/3cf3edae-a5ec-482c-a8d9-866b11397e76
-- statement:
--   (a) If $ x \neq 0$ and $ xy = xz$ then $ y = z$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15286 (x y z : ℝ) (hx : x ≠ 0) : x * y = x * z → y = z   :=  by sorry
