-- Prove2me | Theorems.Thm_case_two_odd_small
-- name    : case_two_odd_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:47:36.377927+00:00
-- url     : https://prove2.me/theorems/48f14890-352d-4965-b879-69509eea5c57
-- title:
--   case two odd small: case two odd small
-- statement:
--   **Subcase (2c):** d₁ and e₁ are both odd, with e₁ ≤ 17 and 3 ∣ e₁.
--       Uses shifted periodic 012-patterns with different shifts for adjacent cycles.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseTwo.lean#L767-L833
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseTwo.lean#L767-L833

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseTwo
set_option autoImplicit true
open Finset Pointwise
variable {m : ℕ} {a b : ℤ}
local notation "d₁" => Nat.gcd b.natAbs m
local notation "d₂" => Nat.gcd (Int.natAbs (b - a)) m
local notation "e₁" => m / d₁

theorem case_two_odd_small (hm : m ≥ 289) (h_gcd_coprime : Nat.gcd d₁ d₂ = 1)
    (h_min : min d₁ d₂ > 1) (hd1_odd : Odd d₁) (he1_div3 : 3 ∣ e₁) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by sorry
