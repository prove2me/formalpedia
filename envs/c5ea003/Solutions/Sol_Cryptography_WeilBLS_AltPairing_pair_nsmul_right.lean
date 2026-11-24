-- Prove2me | solution 1 for Cryptography.WeilBLS.AltPairing.pair_nsmul_right
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:33:01.087291+00:00
-- url     : https://prove2.me/submissions/8f440f3b-f446-4d60-8056-d1f6b8f6064b

import Mathlib
import Definitions.Def_Cryptography_WeilPairingBLS
import Definitions.Def_Cryptography_WeilPairingDeterminant

open scoped BigOperators

open Cryptography.WeilBLS Cryptography.WeilBLS.AltPairing

universe u v

theorem solution {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    (E : AltPairing A μ) (b : ℕ) (x y : A) :
    E.pair x (b • y) = E.pair x y ^ b := by
  simp [pair, map_nsmul]

#print axioms solution
