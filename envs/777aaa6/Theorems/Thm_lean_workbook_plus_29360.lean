-- Prove2me | Theorems.Thm_lean_workbook_plus_29360
-- name    : lean_workbook_plus_29360
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/6109e6a5-0722-428a-aed2-dc096d7282c1
-- statement:
--   $\iff$ (squaring) $5-2\sqrt{2a}=a+2+\frac 1a+a^2-2\sqrt a(a+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29360 : 5 - 2 * Real.sqrt (2 * a) = a + 2 + 1 / a + a^2 - 2 * Real.sqrt a * (a + 1) ↔ 5 - 2 * Real.sqrt (2 * a) = a + 2 + 1 / a + a^2 - 2 * Real.sqrt a * (a + 1)   :=  by sorry
