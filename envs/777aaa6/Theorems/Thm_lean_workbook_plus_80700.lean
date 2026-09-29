-- Prove2me | Theorems.Thm_lean_workbook_plus_80700
-- name    : lean_workbook_plus_80700
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/17b34161-024c-4b44-afba-c00aca037ca9
-- statement:
--   Prove that $ 2\cos a\sin b = \sin(a+b)-\sin(a-b)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80700 : 2 * Real.cos a * Real.sin b = Real.sin (a + b) - Real.sin (a - b)   :=  by sorry
