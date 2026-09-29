-- Prove2me | solution 1 for Heisenberg125.Heis.bsum_of_const
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:05:39.469354+00:00
-- url     : https://prove2.me/submissions/560eb5b8-bb27-40a3-b5b0-f8fd271aa70f

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} {L : List (Heis p)} {β : ZMod p} (h : ∀ g ∈ L, g.b = β) :
    bsum L = β * (L.length : ℕ) := by
  induction L with
  | nil => simp [bsum]
  | cons g L ih =>
    have hg : g.b = β := h g (List.mem_cons_self ..)
    have htail : ∀ x ∈ L, x.b = β := fun x hx => h x (List.mem_cons_of_mem g hx)
    have hb : bsum (g :: L) = g.b + bsum L := by
      simp only [bsum, List.map_cons, List.sum_cons]
    rw [hb, hg, ih htail, List.length_cons]
    push_cast
    ring
