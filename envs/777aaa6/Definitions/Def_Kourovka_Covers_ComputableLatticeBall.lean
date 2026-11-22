-- Prove2me | Definitions.Def_Kourovka_Covers_ComputableLatticeBall
-- name    : Kourovka_Covers_ComputableLatticeBall
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:47:28.125006+00:00
-- url     : https://prove2.me/theorems/3be9ab28-28c9-41f1-a87c-21e0fddc77bd
-- title:
--   Computable Lattice Ball
-- statement:
--   Definitions and structural lemmas for Computable Lattice Ball, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean

import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ComputableLatticeBall
open ComputableIntegers ComputableCoverData
def interval (R : ℕ) : List ℤ :=
  (List.range (2 * R + 1)).map fun (i : ℕ) => (i : ℤ) - R
def cube (R : ℕ) : ℕ → List (List ℤ)
  | 0 => [[]]
  | k + 1 => (interval R).flatMap fun z => (cube R k).map fun v => z :: v
def normSq (v : List ℤ) : ℕ := (v.map fun z => z.natAbs ^ 2).sum
def ball (k R : ℕ) : List (List ℤ) :=
  (cube R k).filter fun v => normSq v < R ^ 2
end Kourovka.MetabelianEnumeration.ComputableLatticeBall


