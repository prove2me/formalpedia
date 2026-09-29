-- Prove2me | solution 1 for Heisenberg125.Heis.card_heis
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:30:50.765133+00:00
-- url     : https://prove2.me/submissions/1a2dda6f-c794-44cf-8f6d-35550b638a85

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 Heis in
theorem solution {p : ℕ} [NeZero p] : Fintype.card (Heis p) = p ^ 3 := by
  have h := Fintype.card_congr (Heis.equivProd (p := p))
  rw [h]
  simp [ZMod.card]
  ring
