-- Prove2me | Theorems.Thm_lean_workbook_plus_22465
-- name    : lean_workbook_plus_22465
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/d58b974c-fa5f-4207-b639-2709e3810b19
-- statement:
--   If $x$ and $y$ are inversely proportional it means that $xy = k$ for some constant $k.$ Basically, if $x$ doubles, $y$ is halved, and other way around.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22465 (x y : ℝ) (h : x * y = k) : (x * 2) * (y / 2) = k   :=  by sorry
