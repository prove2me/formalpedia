-- Prove2me | Theorems.Thm_lean_workbook_plus_68415
-- name    : lean_workbook_plus_68415
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/750fa0cf-ef07-41cb-a04d-fa33b873531d
-- statement:
--   $(2017\cdot 2018-2016\cdot 2019)x^2-(2017\cdot 2018-2016\cdot 2019)4035x=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68415 (x : ℝ) (hx: x ≠ 0) : (2017 * 2018 - 2016 * 2019) * x ^ 2 - (2017 * 2018 - 2016 * 2019) * 4035 * x = 0 ↔ x = 0 ∨ x = 4035   :=  by sorry
