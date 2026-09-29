-- Prove2me | solution 1 for Cryptography.IsogenyFoundations.FreeTrans.unique_connector
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T20:34:04.847716+00:00
-- url     : https://prove2.me/submissions/1eb0d167-9851-480c-beb5-f5ffff25dc34

import Mathlib
import Definitions.Def_Cryptography_AbstractAlgebra_IsogenyFoundations
open Cryptography.IsogenyFoundations in
theorem solution {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq G] [DecidableEq X]
    (T : FreeTrans G X) (x y : X) (g h : G) (hg : T.act g x = y) (hh : T.act h x = y) :
    g = h := by
  -- `h⁻¹ g` fixes `x`, so by freeness it is the identity
  have h1 : T.act (h⁻¹ * g) x = x := by
    rw [T.act_mul, hg, ← hh, ← T.act_mul, inv_mul_cancel, T.act_one]
  have h2 := T.free _ _ h1
  rw [inv_mul_eq_one] at h2
  exact h2.symm
