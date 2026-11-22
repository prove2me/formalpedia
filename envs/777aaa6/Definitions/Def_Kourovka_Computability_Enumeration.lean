-- Prove2me | Definitions.Def_Kourovka_Computability_Enumeration
-- name    : Kourovka_Computability_Enumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:39:41.922335+00:00
-- url     : https://prove2.me/theorems/5e86b5f2-d55f-4d21-ae29-9d287b1e2236
-- title:
--   Enumeration
-- statement:
--   Definitions and structural lemmas for Enumeration, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/Enumeration.lean

import Mathlib.Computability.Halting
import Mathlib.Tactic
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration
def boundedSearch (check : ℕ → ℕ → Bool) (presentation bound : ℕ) : Bool :=
  (List.range bound).any (check presentation)
end Kourovka.MetabelianEnumeration


