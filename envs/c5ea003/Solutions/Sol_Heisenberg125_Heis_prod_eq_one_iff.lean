-- Prove2me | solution 1 for Heisenberg125.Heis.prod_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:10:28.519286+00:00
-- url     : https://prove2.me/submissions/8caa64e9-6dd7-49c6-80b5-5ecbbd72e83d

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} (L : List (Heis p)) :
    L.prod = 1 ↔ asum L = 0 ∧ bsum L = 0 ∧ csum L + crossSum L = 0 := by
  -- the closed form for a list product in the Heisenberg group
  have hprod : ∀ M : List (Heis p),
      M.prod = ⟨asum M, bsum M, csum M + crossSum M⟩ := by
    intro M
    induction M with
    | nil =>
      apply Heis.ext
      · show (0 : ZMod p) = asum []
        simp [asum]
      · show (0 : ZMod p) = bsum []
        simp [bsum]
      · show (0 : ZMod p) = csum [] + crossSum []
        simp [csum, crossSum]
    | cons g M ih =>
      have ha : asum (g :: M) = g.a + asum M := by
        simp only [asum, List.map_cons, List.sum_cons]
      have hb : bsum (g :: M) = g.b + bsum M := by
        simp only [bsum, List.map_cons, List.sum_cons]
      have hc : csum (g :: M) = g.c + csum M := by
        simp only [csum, List.map_cons, List.sum_cons]
      have hx : crossSum (g :: M) = g.a * bsum M + crossSum M := rfl
      rw [List.prod_cons, ih, ha, hb, hc, hx]
      apply Heis.ext
      · show g.a + asum M = g.a + asum M
        rfl
      · show g.b + bsum M = g.b + bsum M
        rfl
      · show g.c + (csum M + crossSum M) + g.a * bsum M
            = g.c + csum M + (g.a * bsum M + crossSum M)
        ring
  rw [hprod L]
  constructor
  · intro h
    have h1 := congrArg Heis.a h
    have h2 := congrArg Heis.b h
    have h3 := congrArg Heis.c h
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact Heis.ext h1 h2 h3
