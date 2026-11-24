-- Prove2me | solution 1 for Cryptography.WeilBLS.AltPairing.pair_add_left
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:32:55.882216+00:00
-- url     : https://prove2.me/submissions/5e148848-cfcb-4901-967b-5683c4ce47dd

import Mathlib
import Definitions.Def_Cryptography_WeilPairingBLS
import Definitions.Def_Cryptography_WeilPairingDeterminant

open scoped BigOperators

open Cryptography.WeilBLS Cryptography.WeilBLS.AltPairing

universe u v

theorem solution {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    (E : AltPairing A μ) (x y z : A) :
    E.pair (x + y) z = E.pair x z * E.pair y z := by
  simp [pair, map_add]

#print axioms solution
