-- Prove2me | Theorems.Thm_lean_workbook_plus_19568
-- name    : lean_workbook_plus_19568
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/622bab01-1191-4957-ab58-443d4be8bf30
-- statement:
--   If $ a > 0$ , prove that \n\n $ \frac {1}{\sqrt {a}} > 2(\sqrt {a + 1} - \sqrt {a})$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19568 (a : ℝ) (ha : 0 < a) : 1 / Real.sqrt a > 2 * (Real.sqrt (a + 1) - Real.sqrt a)   :=  by sorry
