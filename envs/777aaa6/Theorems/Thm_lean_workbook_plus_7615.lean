-- Prove2me | Theorems.Thm_lean_workbook_plus_7615
-- name    : lean_workbook_plus_7615
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/e7034ee5-f351-4519-861e-2572eba387fd
-- statement:
--   $ x + \frac {1}{y} = k\Longleftrightarrow x = \frac {ky - 1}{y}\ \cdots [1]\ \therefore \frac {1}{x} = \frac {y}{ky - 1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7615  (x y k : ℝ)
  (h₀ : x + 1/y = k)
  (h₁ : y ≠ 0)
  (h₂ : k*y - 1 ≠ 0) :
  x = (k*y - 1)/y ∧ 1/x = y/(k*y - 1)   :=  by sorry
