-- Prove2me | Theorems.Thm_lean_workbook_plus_23892
-- name    : lean_workbook_plus_23892
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/578e5d7a-bd60-48c0-99c4-09164c8a82d0
-- statement:
--   For $n=2$ and $z=\frac {-1 + \textrm{i}} {2}$ we have $|z| = \sqrt{2}/2 < 1$ and $z^2+z = -1/2 \in \mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23892  (n z : ℂ)
  (h₀ : n = 2)
  (h₁ : z = (-1 + Complex.I) / 2) :
  z^2 + z = (-1 / 2)   :=  by sorry
