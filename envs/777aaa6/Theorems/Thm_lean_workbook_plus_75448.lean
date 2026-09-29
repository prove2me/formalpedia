-- Prove2me | Theorems.Thm_lean_workbook_plus_75448
-- name    : lean_workbook_plus_75448
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/41367fae-2dae-491d-bda9-aa8560d53c1c
-- statement:
--   $\frac{11+2\cdot 5}{2}<\frac{11+2\sqrt{30}}{2}<\frac{11+2\cdot 6}{2}\Longleftrightarrow \frac{11}{2}<\frac{11+2\sqrt{30}}{2}<\frac{23}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75448 : 11 / 2 < (11 + 2 * Real.sqrt 30) / 2 ∧ (11 + 2 * Real.sqrt 30) / 2 < 23 / 2   :=  by sorry
