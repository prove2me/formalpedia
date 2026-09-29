-- Prove2me | Theorems.Thm_lean_workbook_plus_48740
-- name    : lean_workbook_plus_48740
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/42a294fa-671d-4532-8bd0-1431b53dc313
-- statement:
--   $ 2005=41^2+18^2 \Rightarrow 2005^{2005}=(41 \times 2005^{1002})^2+(18 \times 2005^{1002})^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48740 : 2005 = 41^2 + 18^2 → 2005^2005 = (41 * 2005^1002)^2 + (18 * 2005^1002)^2   :=  by sorry
