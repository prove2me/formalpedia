-- Prove2me | Theorems.Thm_lean_workbook_plus_51451
-- name    : lean_workbook_plus_51451
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b8264f65-264b-4447-a223-3872105cb12a
-- statement:
--   Prove if $r \ge s \ge t \ge u \ge v$ then $r^2 - s^2 + t^2 - u^2 + v^2 \ge (r - s + t - u + v)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51451 (r s t u v : ℝ) (hr : r ≥ s) (hs : s ≥ t) (ht : t ≥ u) (hu : u ≥ v) : r^2 - s^2 + t^2 - u^2 + v^2 ≥ (r - s + t - u + v)^2   :=  by sorry
