-- Prove2me | Theorems.Thm_lean_workbook_plus_14955
-- name    : lean_workbook_plus_14955
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/5b5a02cd-debe-4c71-8e45-73911de1c6bc
-- statement:
--   $ 4 \ge (xy+yz+zx)[4-(xy+yz+zx)],$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14955 {x y z : ℝ} : 4 ≥ (x * y + y * z + z * x) * (4 - (x * y + y * z + z * x))   :=  by sorry
