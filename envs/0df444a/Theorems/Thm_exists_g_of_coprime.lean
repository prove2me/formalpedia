-- Prove2me | Theorems.Thm_exists_g_of_coprime
-- name    : exists_g_of_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:37.893412+00:00
-- url     : https://prove2.me/theorems/8cdf2bb9-9720-4448-aa3c-cd44bb02c405
-- title:
--   exists g of coprime: exists g of coprime
-- statement:
--   **Key reduction for Case 1.** When gcd(b, m) = 1, finds the gap parameter g
--       such that zmod_set m a b = (image of {0,1,g,g+1} under ×b).
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L900-L937
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L900-L937

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem exists_g_of_coprime (a b : ℤ) (hd : Nat.gcd b.natAbs m = 1)
    (hm : 0 < m) (hcard : (zmod_set m a b).card = 4) :
    ∃ g : ℕ, 2 ≤ g ∧ g ≤ m - 2 ∧ zmod_set m a b =
        ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)).image ((b : ZMod m) * ·) := by sorry
