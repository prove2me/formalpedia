-- Prove2me | solution 1 for lean_workbook_plus_30405
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:10:13.128208+00:00
-- url     : https://prove2.me/submissions/58f4c7e8-15a4-4bf8-9e08-52696f80cffe

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum

theorem solution (n : ℤ) : n^2 % 2 = 1 → n % 2 = 1 := by
  intro h
  by_contra hn
  have hrem : n % 2 = 0 := by omega
  norm_num [pow_two, Int.mul_emod, hrem] at h
