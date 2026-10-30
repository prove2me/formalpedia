-- Prove2me | solution 1 for Shamir1979.hierarchical_threshold
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:05:03.125396+00:00
-- url     : https://prove2.me/submissions/c43eb137-b736-45d5-a18d-776f679a7b93

import Mathlib
import Definitions.Def_Shamir1979_Model
import Theorems.Thm_Shamir1979_reconstruction
import Theorems.Thm_Shamir1979_perfect_privacy
open scoped BigOperators
universe u
open Shamir1979

theorem solution (p n k : Nat) [Fact (Nat.Prime p)]
    (hk : 0 < k) (hkn : k ≤ n) (hnp : n < p)
    {A : Type u} (holdings : A → Finset (Fin n)) (coalition : Finset A) :
    (k ≤ (heldLocations holdings coalition).card →
      ∀ (secret : ZMod p) (coins : Coins p k),
        recover (heldLocations holdings coalition)
          (observe (heldLocations holdings coalition) secret coins) = secret) ∧
    ((heldLocations holdings coalition).card < k →
      ∀ (secret : ZMod p) (values : Observation p (heldLocations holdings coalition)),
        observationProbability (k := k) (heldLocations holdings coalition) secret values =
          (1 : Rat) / (p : Rat) ^ (heldLocations holdings coalition).card) :=
  ⟨fun h secret coins => Shamir1979.reconstruction p n k hk hkn hnp secret coins _ h,
   fun h secret values => Shamir1979.perfect_privacy p n k hk hkn hnp _ h secret values⟩
