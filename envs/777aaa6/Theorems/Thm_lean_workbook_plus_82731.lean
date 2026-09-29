-- Prove2me | Theorems.Thm_lean_workbook_plus_82731
-- name    : lean_workbook_plus_82731
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/4011f002-8367-42fe-bccf-1a75952d3537
-- statement:
--   Put $~~~h-3=z^2~~~\implies~~h=z^2+3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82731 (h z : ℤ) (hz: h - 3 = z^2) : h = z^2 + 3   :=  by sorry
