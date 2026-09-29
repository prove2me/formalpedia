-- Prove2me | Theorems.Thm_lean_workbook_plus_63386
-- name    : lean_workbook_plus_63386
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/0b9ec974-6368-4925-9fc8-42edb11469c0
-- statement:
--   Prove that the set $\{(x,y):xy=1\}$ is closed in the Euclidean metric space $(\mathbb{R}^2, d)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63386 : IsClosed {p : ℝ × ℝ | p.fst * p.snd = 1}   :=  by sorry
