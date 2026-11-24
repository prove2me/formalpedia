-- Prove2me | solution 1 for Cryptography.WeilBLS.AltPairing.pair_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:33:02.039882+00:00
-- url     : https://prove2.me/submissions/17bde5fe-6e91-4938-b869-ca7b223c946f

import Mathlib
import Definitions.Def_Cryptography_WeilPairingBLS
import Definitions.Def_Cryptography_WeilPairingDeterminant

open scoped BigOperators

open Cryptography.WeilBLS Cryptography.WeilBLS.AltPairing

universe u v

theorem solution {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    (E : AltPairing A μ) (y : A) :
    E.pair 0 y = 1 := by
  simp [pair]

#print axioms solution
