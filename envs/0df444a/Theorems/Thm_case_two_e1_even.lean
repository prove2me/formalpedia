-- Prove2me | Theorems.Thm_case_two_e1_even
-- name    : case_two_e1_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:47:34.908515+00:00
-- url     : https://prove2.me/theorems/b94922b0-eae7-4278-9cbe-eccaa6674ba0
-- title:
--   case two e1 even: case two e1 even
-- statement:
--   **Subcase (2a).** $e_1$ is even. Each cycle uses two alternating colors;
--       adjacent cycles skip different colors. The simplest of the four subcases.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseTwo.lean#L276-L282
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseTwo.lean#L276-L282

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseTwo
set_option autoImplicit true
open Finset Pointwise
variable {m : ℕ} {a b : ℤ}
local notation "d₁" => Nat.gcd b.natAbs m
local notation "d₂" => Nat.gcd (Int.natAbs (b - a)) m
local notation "e₁" => m / d₁

theorem case_two_e1_even (hm : m ≥ 289) (h_gcd_coprime : Nat.gcd d₁ d₂ = 1)
    (h_min : min d₁ d₂ > 1) (he1_even : Even e₁) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by sorry
