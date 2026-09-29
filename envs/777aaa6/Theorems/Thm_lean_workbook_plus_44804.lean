-- Prove2me | Theorems.Thm_lean_workbook_plus_44804
-- name    : lean_workbook_plus_44804
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/7c8334d2-212d-4efb-9ba8-eaa2c7ca1263
-- statement:
--   Show that the function $f(t) = (\cos t, \sin t)$ is continuous.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44804 : Continuous fun t => (cos t, sin t)   :=  by sorry
