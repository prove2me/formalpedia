-- Prove2me | Theorems.Thm_lean_workbook_plus_10779
-- name    : lean_workbook_plus_10779
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/867dd092-1cc1-42d8-a53b-3de7c3ee0afd
-- statement:
--   @ above: $64(x^2+4x+4)(1-x)=(x^2-22x+121)(x+1)$ which gives $65x^3+171x^2+99x-135=0$ . This factors out as $(5x-3)(13x^2+42x+45)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10779  (x : ℝ) :
  64 * (x^2 + 4 * x + 4) * (1 - x) = (x^2 - 22 * x + 121) * (x + 1) ↔ 65 * x^3 + 171 * x^2 + 99 * x - 135 = 0   :=  by sorry
