-- Prove2me | Theorems.Thm_gcd_coprime_of_gcd_abc
-- name    : gcd_coprime_of_gcd_abc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:48:09.234952+00:00
-- url     : https://prove2.me/theorems/e21ec4e9-37ea-4ac3-8f28-f618ca439cb0
-- title:
--   gcd coprime of gcd abc: gcd coprime of gcd abc
-- statement:
--   Auxiliary: the coprimality gcd(d₁, d₂) = 1 follows from gcd(a, b, c) = 1.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi.lean#L87-L111
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi.lean#L87-L111

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Definitions.Def_Polychromatic_FourThree_Combi_CaseTwo
import Definitions.Def_Polychromatic_FourThree_Combi
set_option autoImplicit true
open Finset Pointwise

theorem gcd_coprime_of_gcd_abc {a b c : ℤ} {m : ℕ}
    (hm : (m : ℤ) = c - a + b) (hgcd : Finset.gcd {a, b, c} id = 1) :
    (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1 := by sorry
