-- Prove2me | Theorems.Thm_lean_workbook_plus_2036
-- name    : lean_workbook_plus_2036
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ad4ee478-b326-47c8-8928-9921893fe897
-- statement:
--   Express $x$ and $y$ in terms of $t$ and $a$ as $x=asint$, $y=acost$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2036 (x y t a : ℝ) : x = a * Real.sin t ∧ y = a * Real.cos t ↔ x = a * Real.sin t ∧ y = a * Real.cos t   :=  by sorry
