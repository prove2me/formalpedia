-- Prove2me | Theorems.Thm_lean_workbook_plus_11829
-- name    : lean_workbook_plus_11829
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/4e61f5ca-85b9-4d4d-ad3c-46b49b6aab6e
-- statement:
--   For the positive real numbers $ a,\ b,\ c$ , prove that $ \frac{2007c}{2008a+2009b}+\frac{2008a}{2009b+2007c}+\frac{2009b}{2007c+2008a}\geq \frac{3}{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11829 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2007 * c / (2008 * a + 2009 * b) + 2008 * a / (2009 * b + 2007 * c) + 2009 * b / (2007 * c + 2008 * a)) ≥ 3 / 2   :=  by sorry
