-- Prove2me | Theorems.Thm_lean_workbook_plus_51664
-- name    : lean_workbook_plus_51664
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/e4ec46a7-d4e7-4d0c-b260-a0bf6f486c11
-- statement:
--   If $ a,b,c > 0$ , then \n\n $ \frac {ab + bc + ca}{a^2 + b^2 + c^2} \leq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51664 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≤ 1   :=  by sorry
