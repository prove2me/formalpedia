-- Prove2me | Theorems.Thm_lean_workbook_plus_79307
-- name    : lean_workbook_plus_79307
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/5b4b7a3e-4c12-44bf-aa96-c7030635bb2f
-- statement:
--   For $a,b,c\ge 0$ prove that : \n\n $a^3b^2+b^3a^2+b^3c^2+c^3b^2+c^3a^2+a^3c^2\ge abc (a^2+b^2+c^2+ab+bc+ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79307 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a^3 * b^2 + b^3 * a^2 + b^3 * c^2 + c^3 * b^2 + c^3 * a^2 + a^3 * c^2 ≥ a * b * c * (a^2 + b^2 + c^2 + a * b + b * c + c * a)   :=  by sorry
