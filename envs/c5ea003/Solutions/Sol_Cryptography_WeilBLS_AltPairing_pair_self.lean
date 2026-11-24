-- Prove2me | solution 1 for Cryptography.WeilBLS.AltPairing.pair_self
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:32:57.68469+00:00
-- url     : https://prove2.me/submissions/ecaf45e7-210c-4af7-bcec-2fb4e3cdaaca

import Mathlib
import Definitions.Def_Cryptography_WeilPairingBLS
import Definitions.Def_Cryptography_WeilPairingDeterminant

open scoped BigOperators

open Cryptography.WeilBLS Cryptography.WeilBLS.AltPairing

universe u v

theorem solution {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    (E : AltPairing A μ) (x : A) :
    E.pair x x = 1 := by
  simp [pair, E.alternating x]

#print axioms solution
