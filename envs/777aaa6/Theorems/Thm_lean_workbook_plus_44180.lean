-- Prove2me | Theorems.Thm_lean_workbook_plus_44180
-- name    : lean_workbook_plus_44180
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/1a134c10-d641-4089-8f37-f9b1186c3eb4
-- statement:
--   Consider the cases: 1) $ \frac {a}{2} < 0$, 2) $ 0\le \frac {a}{2} \le 2$, 3) $ \frac {a}{2} > 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44180 (a : ℝ) : a / 2 < 0 ∨ 0 ≤ a / 2 ∧ a / 2 ≤ 2 ∨ a / 2 > 2   :=  by sorry
