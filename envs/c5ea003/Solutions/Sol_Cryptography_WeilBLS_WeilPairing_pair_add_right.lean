-- Prove2me | solution 1 for Cryptography.WeilBLS.WeilPairing.pair_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T01:09:20.663383+00:00
-- url     : https://prove2.me/submissions/4d907ece-c654-4be9-a486-6632f3716bce

import Definitions.Def_Cryptography_WeilPairingBLS

open Cryptography.WeilBLS

open Cryptography.WeilBLS in
/-- **Bilinearity in the second argument**: the Weil pairing turns addition of torsion
points into multiplication in `μ`. -/
theorem solution {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {n : ℕ}
    {μ : Type*} [CommGroup μ] (e : WeilPairing W n μ) (P Q R : torsionPoints W n) :
    e.pair P (Q + R) = e.pair P Q * e.pair P R := by
  simp only [WeilPairing.pair, map_add, toMul_add]
