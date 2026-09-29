-- Prove2me | Theorems.Thm_lean_workbook_plus_4043
-- name    : lean_workbook_plus_4043
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/129a21ab-5bef-49c0-bb7e-982e5273b817
-- statement:
--   If $2\sqrt{6} + 5 = 10$, then $\sqrt{6} = 2.5$. Show that $5 + \sqrt{6}$ is less than 10.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4043 : 2 * Real.sqrt 6 + 5 = 10 → 5 + Real.sqrt 6 < 10   :=  by sorry
