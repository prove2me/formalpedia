-- Prove2me | Theorems.Thm_lean_workbook_plus_38763
-- name    : lean_workbook_plus_38763
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/ecccb324-3fa0-43de-bd7c-8dbc6aefeabd
-- statement:
--   If $ a > 0$ , prove that \n\n $ \frac {1}{\sqrt {a}} > 2(\sqrt {a + 1} - \sqrt {a})$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38763 (a : ℝ) (h : a > 0) : 1 / Real.sqrt a > 2 * (Real.sqrt (a + 1) - Real.sqrt a)   :=  by sorry
