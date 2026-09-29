-- Prove2me | solution 1 for Cryptography.WeilBLS.WeilPairing.bilinear_right
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T01:31:43.764278+00:00
-- url     : https://prove2.me/submissions/24ed976b-ef61-4653-89af-c83fbbe48ed2

import Definitions.Def_Cryptography_WeilPairingBLS

open Cryptography.WeilBLS

open Cryptography.WeilBLS in
/-- **Scalar bilinearity in the second argument**: scaling the second torsion point by `b`
raises the pairing to the power `b`. -/
theorem solution {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {n : ℕ}
    {μ : Type*} [CommGroup μ] (e : WeilPairing W n μ) (b : ℕ) (P Q : torsionPoints W n) :
    e.pair P (b • Q) = e.pair P Q ^ b := by
  simp only [WeilPairing.pair, map_nsmul, toMul_nsmul]
