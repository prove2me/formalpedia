-- Prove2me | Definitions.Def_mme_CW_2376_profile_induced_family
-- name    : mme_CW_2376_profile_induced_family
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T17:08:06.202649+00:00
-- url     : https://prove2.me/theorems/810e36bb-7f4c-4e68-86c8-59d78e9b7d50
-- title:
--   Induced exact-profile families for CW pruning
-- statement:
--   Given three exact-profile addresses $x,y,z$, form their mixed address by taking the mode-zero word from $x$, the mode-one word from $y$, and the mode-two word from $z$. The mixed address is coordinatewise supported when its three grades sum to four at every tensor-square coordinate.
--
--   A retained family $F$ is induced if every supported mixed address formed from members $x,y,z$ of $F$ forces
--
--   $$
--   x=y=z.
--   $$
--
--   The combined pruning predicate requires both this induced property and mode-disjointness. This is precisely what is needed after variable zeroing: mode-disjointness prevents shared variables, while inducedness rules out unintended mixed tensor blocks assembled from variables belonging to different retained addresses.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square support I+J+K=4 and Salem--Spencer collision pruning on journal pp. 265 and 267--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_2376_profile_address

namespace MME

def cw2376MixedAddress {m : ℕ}
    (x y z : CW2376ProfileAddress m) : CW2376ProfileAddress m
  | ⟨0, _⟩ => x 0
  | ⟨1, _⟩ => y 1
  | ⟨2, _⟩ => z 2
  | ⟨_ + 3, h⟩ => absurd h (by omega)

def CW2376CoordinatewiseSupported {m : ℕ}
    (a : CW2376ProfileAddress m) : Prop :=
  ∀ j : Fin (cw2376ProfileLength m),
    (a 0 j).val + (a 1 j).val + (a 2 j).val = 4

def CW2376Induced {m : ℕ}
    (F : Finset (CW2376ExactProfileAddress m)) : Prop :=
  ∀ x : F, ∀ y : F, ∀ z : F,
    CW2376CoordinatewiseSupported
      (cw2376MixedAddress x.1.1 y.1.1 z.1.1) →
    x = y ∧ y = z

def CW2376InducedModeDisjoint {m : ℕ}
    (F : Finset (CW2376ExactProfileAddress m)) : Prop :=
  CW2376ModeDisjoint F ∧ CW2376Induced F

end MME


