-- Prove2me | Theorems.Thm_lean_workbook_plus_4590
-- name    : lean_workbook_plus_4590
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/918ebac2-c413-409a-9114-2b8bed189d76
-- statement:
--   Express $\sqrt{2}$ in terms of cosine: $\sqrt{2} = 2\cos\left(\frac{\pi}{4}\right)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4590 : 2 * Real.cos (Real.pi / 4) = Real.sqrt 2   :=  by sorry
