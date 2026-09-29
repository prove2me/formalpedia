-- Prove2me | solution 1 for Heisenberg125.Heis.prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:45:24.785895+00:00
-- url     : https://prove2.me/submissions/e1f601f2-8e11-4bb4-98b7-d000d8448c5f

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} (L : List (Heis p)) :
    L.prod = ⟨asum L, bsum L, csum L + crossSum L⟩ := by
  induction L with
  | nil =>
    apply Heis.ext
    · show (0 : ZMod p) = asum []
      simp [asum]
    · show (0 : ZMod p) = bsum []
      simp [bsum]
    · show (0 : ZMod p) = csum [] + crossSum []
      simp [csum, crossSum]
  | cons g L ih =>
    have ha : asum (g :: L) = g.a + asum L := by
      simp only [asum, List.map_cons, List.sum_cons]
    have hb : bsum (g :: L) = g.b + bsum L := by
      simp only [bsum, List.map_cons, List.sum_cons]
    have hc : csum (g :: L) = g.c + csum L := by
      simp only [csum, List.map_cons, List.sum_cons]
    have hx : crossSum (g :: L) = g.a * bsum L + crossSum L := rfl
    rw [List.prod_cons, ih, ha, hb, hc, hx]
    apply Heis.ext
    · show g.a + asum L = g.a + asum L
      rfl
    · show g.b + bsum L = g.b + bsum L
      rfl
    · show g.c + (csum L + crossSum L) + g.a * bsum L
          = g.c + csum L + (g.a * bsum L + crossSum L)
      ring
