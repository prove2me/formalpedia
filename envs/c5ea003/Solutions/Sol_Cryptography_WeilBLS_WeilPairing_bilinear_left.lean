-- Prove2me | solution 1 for Cryptography.WeilBLS.WeilPairing.bilinear_left
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T01:26:13.558196+00:00
-- url     : https://prove2.me/submissions/d52243bb-f1c6-46af-9a1f-c1e145d12a2c

import Definitions.Def_Cryptography_WeilPairingBLS

open Cryptography.WeilBLS

open Cryptography.WeilBLS in
/-- **Scalar bilinearity in the first argument**: scaling the first torsion point by `a`
raises the pairing to the power `a`. -/
theorem solution {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {n : ℕ}
    {μ : Type*} [CommGroup μ] (e : WeilPairing W n μ) (a : ℕ) (P Q : torsionPoints W n) :
    e.pair (a • P) Q = e.pair P Q ^ a := by
  simp only [WeilPairing.pair, map_nsmul, AddMonoidHom.nsmul_apply, toMul_nsmul]
