-- Prove2me | solution 1 for Cryptography.WeilBLS.AltPairing.pair_zsmul_left
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:32:58.49796+00:00
-- url     : https://prove2.me/submissions/aa5f6998-b3d1-4488-b9f8-ecaa7fca3463

import Mathlib
import Definitions.Def_Cryptography_WeilPairingBLS
import Definitions.Def_Cryptography_WeilPairingDeterminant

open scoped BigOperators

open Cryptography.WeilBLS Cryptography.WeilBLS.AltPairing

universe u v

theorem solution {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    (E : AltPairing A μ) (a : ℤ) (x y : A) :
    E.pair (a • x) y = E.pair x y ^ a := by
  simp [pair, map_zsmul]

#print axioms solution
