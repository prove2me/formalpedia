-- Prove2me | solution 2 for Heisenberg125.Heis.commute_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:36:20.442984+00:00
-- url     : https://prove2.me/submissions/318d82c9-7ab1-4fdf-a55f-e115772e88d6

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic

open Heisenberg125 Heis

variable {p : ℕ}

theorem solution {g h : Heis p} : Commute g h ↔ g.a * h.b = h.a * g.b := by
  constructor
  · intro hg
    have hc := congrArg Heis.c hg.eq
    simp only [mul_c] at hc
    have := congrArg (fun x : ZMod p => x - g.c - h.c) hc
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  · intro hcross
    change g * h = h * g
    ext
    · simp [mul_a, add_comm]
    · simp [mul_b, add_comm]
    · simp [mul_c, hcross, add_comm, add_left_comm, add_assoc]
