-- Prove2me | Theorems.Thm_lean_workbook_plus_60949
-- name    : lean_workbook_plus_60949
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/01a0a9c7-ff8b-4699-8a19-971a91c1dc38
-- statement:
--   Prove that for all real number of $x$ , then $\vert\sin{x}\vert + \vert\cos{x}\vert \geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60949 (x : ℝ) : abs (sin x) + abs (cos x) ≥ 1   :=  by sorry
