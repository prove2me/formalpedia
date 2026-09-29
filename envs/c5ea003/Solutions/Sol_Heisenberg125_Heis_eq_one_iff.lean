-- Prove2me | solution 1 for Heisenberg125.Heis.eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:16:26.201633+00:00
-- url     : https://prove2.me/submissions/2fede838-843c-4907-8f79-18feff20712a

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} {g : Heis p} : g = 1 ↔ g.a = 0 ∧ g.b = 0 ∧ g.c = 0 := by
  constructor
  · intro h
    subst h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨ha, hb, hc⟩
    exact Heis.ext ha hb hc
