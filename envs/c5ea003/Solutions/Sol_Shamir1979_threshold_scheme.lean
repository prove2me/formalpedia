-- Prove2me | solution 1 for Shamir1979.threshold_scheme
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:05:01.795992+00:00
-- url     : https://prove2.me/submissions/56813737-8df3-4c41-913f-f3135902307c

import Mathlib
import Definitions.Def_Shamir1979_Model
import Theorems.Thm_Shamir1979_reconstruction
import Theorems.Thm_Shamir1979_perfect_privacy
open scoped BigOperators
universe u
open Shamir1979

theorem solution (p n k : Nat) [Fact (Nat.Prime p)]
    (hk : 0 < k) (hkn : k ≤ n) (hnp : n < p) :
    (∀ (secret : ZMod p) (coins : Coins p k) (Γ : Finset (Fin n)),
      k ≤ Γ.card → recover Γ (observe Γ secret coins) = secret) ∧
    (∀ (secret : ZMod p) (Γ : Finset (Fin n)) (values : Observation p Γ),
      Γ.card < k → observationProbability (k := k) Γ secret values =
        (1 : Rat) / (p : Rat) ^ Γ.card) :=
  ⟨fun secret coins Γ h => Shamir1979.reconstruction p n k hk hkn hnp secret coins Γ h,
   fun secret Γ values h => Shamir1979.perfect_privacy p n k hk hkn hnp Γ h secret values⟩
