-- Prove2me | solution 1 for lean_workbook_plus_80985
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:38:53.725424+00:00
-- url     : https://prove2.me/submissions/52e92070-7bc9-49ec-8393-7c21cda25064

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith

theorem solution (x : ℝ) (h : ⌊x+2⌋ = 1) : x ∈ Set.Icc (-1) 0 := by
  have hl := Int.floor_le (x+2)
  have hu := Int.lt_floor_add_one (x+2)
  rw [h] at hl hu
  norm_num at hl hu
  constructor <;> linarith
