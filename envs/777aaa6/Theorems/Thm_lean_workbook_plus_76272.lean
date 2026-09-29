-- Prove2me | Theorems.Thm_lean_workbook_plus_76272
-- name    : lean_workbook_plus_76272
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/cd7a2c3d-bc98-4601-9d8c-fb9ac81eedb2
-- statement:
--   Illustrate the addition rule in modular arithmetic using the example: $12 = 2\mod5$, show that $12 + 1 = 2 + 1\mod5$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76272 : 12 + 1 ≡ (2 + 1) [ZMOD 5]   :=  by sorry
