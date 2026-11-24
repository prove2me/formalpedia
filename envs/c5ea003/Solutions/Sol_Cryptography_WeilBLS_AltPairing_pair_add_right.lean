-- Prove2me | solution 1 for Cryptography.WeilBLS.AltPairing.pair_add_right
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:32:56.684915+00:00
-- url     : https://prove2.me/submissions/77ccfe0e-6993-4a96-88c9-c5c10ceae678

import Mathlib
import Definitions.Def_Cryptography_WeilPairingBLS
import Definitions.Def_Cryptography_WeilPairingDeterminant

open scoped BigOperators

open Cryptography.WeilBLS Cryptography.WeilBLS.AltPairing

universe u v

theorem solution {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    (E : AltPairing A μ) (x y z : A) :
    E.pair x (y + z) = E.pair x y * E.pair x z := by
  simp [pair, map_add]

#print axioms solution
