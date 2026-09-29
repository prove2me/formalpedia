-- Prove2me | solution 1 for Cryptography.WeilBLS.BLSParams.forgery_solves_cdh
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T01:37:02.217472+00:00
-- url     : https://prove2.me/submissions/57e13614-514f-45a3-90e8-931c1ec5c563

import Definitions.Def_Cryptography_WeilPairingBLS

open Cryptography.WeilBLS Cryptography.WeilBLS.BLSParams

open Cryptography.WeilBLS Cryptography.WeilBLS.BLSParams in
/-- **A valid forgery on the programmed message solves CDH**: any signature that verifies
under `publicA` on the target message equals the CDH target `secretA • publicB`. -/
theorem solution {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {n : ℕ}
    {μ : Type*} [CommGroup μ] (P : BLSParams W n μ) {Message : Type*} [DecidableEq Message]
    (game : ProgrammedFreshChallenge P Message)
    (forgedSignature : torsionPoints W n)
    (valid : P.verifies game.challenge.publicA
      (game.hashToCurve game.targetMessage) forgedSignature) :
    forgedSignature = game.challenge.target := by
  unfold BLSParams.verifies at valid
  rw [game.programmed, game.challenge.publicA_eq] at valid
  apply P.pairing_generator_injective
  show P.pairing.pair forgedSignature P.generator = P.pairing.pair game.challenge.target P.generator
  rw [valid]
  simp only [BLSParams.publicKey, BLSParams.CDHChallenge.target, WeilPairing.pair, map_nsmul,
    AddMonoidHom.nsmul_apply, toMul_nsmul]
