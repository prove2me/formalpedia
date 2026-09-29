-- Prove2me | solution 1 for Heisenberg125.Heis.mem_center_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T00:45:33.988187+00:00
-- url     : https://prove2.me/submissions/d5a2267b-dc5e-4ab2-805e-101b8b6538f2

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_Structure
open Heisenberg125 in
theorem solution {p : ℕ} {g : Heis p} :
    g ∈ Subgroup.center (Heis p) ↔ g.a = 0 ∧ g.b = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · -- commuting with `x = (1,0,0)` kills `b`, commuting with `y = (0,1,0)` kills `a`
    intro h
    have hx := congrArg Heis.c (h (Heis.x p))
    have hy := congrArg Heis.c (h (Heis.y p))
    simp only [Heis.mul_c, Heis.x, Heis.y] at hx hy
    constructor
    · linear_combination -hy
    · linear_combination hx
  · rintro ⟨ha, hb⟩ h
    ext <;> simp [ha, hb] <;> ring
