-- Prove2me | Theorems.Thm_lean_workbook_plus_7177
-- name    : lean_workbook_plus_7177
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f04f9ff4-8117-42bf-8279-f330a3fe44d7
-- statement:
--   If $ (a,b,c)$ is a solution then $ (k a, k b, k c)$ is also a solution
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7177 {a b c : ℝ} (h : a^2 + b^2 = c^2) : ∃ k : ℝ, k^2 * a^2 + k^2 * b^2 = k^2 * c^2   :=  by sorry
