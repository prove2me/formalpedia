-- Prove2me | solution 1 for Heisenberg125.Heis.crossSum_eq_zero_of_a_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:00:47.277082+00:00
-- url     : https://prove2.me/submissions/d894c946-4166-4afa-af5e-5370b99a053d

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} {L : List (Heis p)} (h : ∀ g ∈ L, g.a = 0) :
    crossSum L = 0 := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    have hg : g.a = 0 := h g (List.mem_cons_self ..)
    have htail : ∀ x ∈ L, x.a = 0 := fun x hx => h x (List.mem_cons_of_mem g hx)
    show g.a * bsum L + crossSum L = 0
    rw [hg, ih htail, zero_mul, add_zero]
