-- Prove2me | solution 1 for IwasawaMonoidHom.lambdaInv_C_pow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T22:41:57.844992+00:00
-- url     : https://prove2.me/submissions/35cd0c7e-c9df-4e84-87f4-1433cc48e259

import Mathlib
import Definitions.Def_Bridges_MatsunoIwasawaMonoidHom
open IwasawaMonoidHom Polynomial in
theorem solution (p : ℕ) [Fact p.Prime] (k : ℕ) : lambdaInv p (C ((p : ℤ) ^ k)) = 0 := by
  unfold lambdaInv reduce
  -- the primitive part of a constant is a constant, so its reduction has trailing degree `0`
  have h1 : (C ((p : ℤ) ^ k)).primPart.natDegree = 0 := by
    rw [Polynomial.natDegree_primPart, Polynomial.natDegree_C]
  apply Nat.eq_zero_of_le_zero
  calc _ ≤ ((C ((p : ℤ) ^ k)).primPart.map (Int.castRingHom (ZMod p))).natDegree :=
        Polynomial.natTrailingDegree_le_natDegree _
    _ ≤ (C ((p : ℤ) ^ k)).primPart.natDegree := Polynomial.natDegree_map_le
    _ = 0 := h1
