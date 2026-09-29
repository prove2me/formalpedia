-- Prove2me | Theorems.Thm_lean_workbook_plus_44100
-- name    : lean_workbook_plus_44100
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/49d37d67-ce4a-4def-8ba5-8445c2d2aebe
-- statement:
--   $(x+y+z)^2-6(x+y+z)+9\ge 0\iff (x+y+z-3)^2\ge0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44100 : (x + y + z - 3) ^ 2 ≥ 0 ↔ (x + y + z) ^ 2 - 6 * (x + y + z) + 9 ≥ 0   :=  by sorry
