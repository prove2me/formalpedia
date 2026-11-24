-- Prove2me | solution 1 for Cryptography.WeilBLS.AltPairing.pair_zsmul_right
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:32:59.285247+00:00
-- url     : https://prove2.me/submissions/fd4e0fd8-b008-486b-90ef-4f4b0fad08c9

import Mathlib
import Definitions.Def_Cryptography_WeilPairingBLS
import Definitions.Def_Cryptography_WeilPairingDeterminant

open scoped BigOperators

open Cryptography.WeilBLS Cryptography.WeilBLS.AltPairing

universe u v

theorem solution {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    (E : AltPairing A μ) (b : ℤ) (x y : A) :
    E.pair x (b • y) = E.pair x y ^ b := by
  simp [pair, map_zsmul]

#print axioms solution
