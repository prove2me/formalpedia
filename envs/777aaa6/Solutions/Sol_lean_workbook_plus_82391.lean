-- Prove2me | solution 1 for lean_workbook_plus_82391
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:07:08.337516+00:00
-- url     : https://prove2.me/submissions/49cb757c-8c97-48cc-bb75-ec879cfecdc7

import Mathlib

theorem solution (R : Type*) [CommRing R] (I J : Ideal R)
    (h : I + J = ⊤) : I * J = I ⊓ J := by
  exact Ideal.mul_eq_inf_of_coprime h
