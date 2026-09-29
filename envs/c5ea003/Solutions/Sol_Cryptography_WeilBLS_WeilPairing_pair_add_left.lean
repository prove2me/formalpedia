-- Prove2me | solution 1 for Cryptography.WeilBLS.WeilPairing.pair_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T01:21:33.170701+00:00
-- url     : https://prove2.me/submissions/5d712f49-7c4b-4b59-97ab-fc48872348c8

import Definitions.Def_Cryptography_WeilPairingBLS

open Cryptography.WeilBLS

open Cryptography.WeilBLS in
/-- **Bilinearity in the first argument**: the Weil pairing turns addition of torsion
points into multiplication in `μ`. -/
theorem solution {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {n : ℕ}
    {μ : Type*} [CommGroup μ] (e : WeilPairing W n μ) (P Q R : torsionPoints W n) :
    e.pair (P + Q) R = e.pair P R * e.pair Q R := by
  simp only [WeilPairing.pair, map_add, AddMonoidHom.add_apply, toMul_add]
