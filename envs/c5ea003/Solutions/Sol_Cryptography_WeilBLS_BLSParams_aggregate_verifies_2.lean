-- Prove2me | solution 2 for Cryptography.WeilBLS.BLSParams.aggregate_verifies
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T01:15:17.111007+00:00
-- url     : https://prove2.me/submissions/a9d62051-7452-4f93-888f-717808adf660

import Definitions.Def_Cryptography_WeilPairingBLS

open Cryptography.WeilBLS

open Cryptography.WeilBLS in
/-- **Aggregate BLS verification**: the pairing of an aggregated signature with the
generator is the product of the individual verification pairings. -/
theorem solution {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {n : ℕ}
    {μ : Type*} [CommGroup μ] (P : BLSParams W n μ) {ι : Type*} (s : Finset ι)
    (sk : ι → ℕ) (hashPoint : ι → torsionPoints W n) :
    P.pairing.pair (BLSParams.aggregate s (fun i => P.sign (sk i) (hashPoint i))) P.generator =
      ∏ i ∈ s, P.pairing.pair (hashPoint i) (P.publicKey (sk i)) := by
  simp only [WeilPairing.pair, BLSParams.aggregate, BLSParams.sign, BLSParams.publicKey,
    map_sum, map_nsmul, AddMonoidHom.finset_sum_apply, AddMonoidHom.nsmul_apply,
    toMul_sum, toMul_nsmul]
