-- Prove2me | solution 1 for Cryptography.WeilBLS.AltPairing.pair_nsmul_left
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:33:00.003423+00:00
-- url     : https://prove2.me/submissions/1188ba64-94f0-4964-a056-da3696bd8934

import Mathlib
import Definitions.Def_Cryptography_WeilPairingBLS
import Definitions.Def_Cryptography_WeilPairingDeterminant

open scoped BigOperators

open Cryptography.WeilBLS Cryptography.WeilBLS.AltPairing

universe u v

theorem solution {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    (E : AltPairing A μ) (a : ℕ) (x y : A) :
    E.pair (a • x) y = E.pair x y ^ a := by
  simp [pair, map_nsmul]

#print axioms solution
