-- Prove2me | Definitions.Def_Kourovka_Computability_ComputableIntegers
-- name    : Kourovka_Computability_ComputableIntegers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:42:49.46205+00:00
-- url     : https://prove2.me/theorems/9b1660cc-b7f8-4a95-b3c9-573398524f62
-- title:
--   Computable Integers
-- statement:
--   Definitions and structural lemmas for Computable Integers, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean

import Definitions.Def_Kourovka_Computability_ComputablePresentations
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
instance integerPrimcodable : Primcodable ℤ :=
  Primcodable.ofEquiv (ℕ ⊕ ℕ) Equiv.intEquivNatSumNat
def subNat (m n : ℕ) : ℤ :=
  if n ≤ m then ((m - n : ℕ) : ℤ) else Int.negSucc (n - m - 1)
end Kourovka.MetabelianEnumeration.ComputableIntegers


