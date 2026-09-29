-- Prove2me | Theorems.Thm_lean_workbook_plus_41639
-- name    : lean_workbook_plus_41639
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/b8d596a0-bfc0-4982-beab-27bb3d306c3a
-- statement:
--   If $ a > 0$ , prove that \n\n $ \frac {1}{\sqrt {a}} > 2(\sqrt {a + 1} - \sqrt {a})$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41639 (a : ℝ) (h : a > 0) : (1 / Real.sqrt a) > 2 * (Real.sqrt (a + 1) - Real.sqrt a)   :=  by sorry
