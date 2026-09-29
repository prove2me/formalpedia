-- Prove2me | solution 1 for Heisenberg125.Heis.commute_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:31:54.894978+00:00
-- url     : https://prove2.me/submissions/3c0686f4-4b5c-4ac9-9cb8-ccce6a2fe44b

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 Heis in
theorem solution {p : ℕ} {g h : Heis p} : Commute g h ↔ g.a * h.b = h.a * g.b := by
  constructor
  · intro hc
    have h3 := congrArg Heis.c hc
    simp only [Heis.mul_c] at h3
    linear_combination h3
  · intro he
    show g * h = h * g
    refine Heis.ext ?_ ?_ ?_
    · simp only [Heis.mul_a]
      ring
    · simp only [Heis.mul_b]
      ring
    · simp only [Heis.mul_c]
      linear_combination he
