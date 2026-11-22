-- Prove2me | Definitions.Def_Kourovka_Polyhedral_ComputableCone
-- name    : Kourovka_Polyhedral_ComputableCone
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:44:22.707702+00:00
-- url     : https://prove2.me/theorems/9f783fe8-7303-48ba-9911-9acbbe5d6ddd
-- title:
--   Computable Cone
-- statement:
--   Definitions and structural lemmas for Computable Cone, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
abbrev VectorCode := List ℤ
abbrev SupportsCode := List (List VectorCode)
def decodeVector (n : ℕ) (v : VectorCode) : ConeVerifier.Vec n :=
  fun i => (v.getD i 0 : ℚ)
def decodeSupports (n : ℕ) (supports : SupportsCode) : ConeVerifier.Supports n :=
  supports.map fun s => s.map (decodeVector n)
def supportRow (r : ℕ) (v : VectorCode) : RowCode :=
  (v.map fun z => (2 ^ r : ℤ) * z, -1)
def coordinate (n i : ℕ) (a b : ℤ) : RowCode :=
  ((List.range n).map fun j => if j = i then a else 0, b)
def cubeRows (n : ℕ) : List RowCode :=
  (List.range n).flatMap fun i => [coordinate n i 1 (-1), coordinate n i (-1) (-1)]
def faceRows (n i : ℕ) (sign : ℤ) : List RowCode :=
  [coordinate n i 1 (-sign), coordinate n i (-1) sign] ++ cubeRows n
def choices (r : ℕ) : SupportsCode → List (List RowCode)
  | [] => [[]]
  | support :: rest => support.flatMap fun u => (choices r rest).map fun rows => supportRow r u :: rows
def badDirection (nr : ℕ × ℕ) (supports : SupportsCode) : Bool :=
  (List.range nr.1).any fun i => ([-1, 1] : List ℤ).any fun sign =>
    (choices nr.2 supports).any fun rows =>
      ComputableFourierMotzkin.check nr.1 (rows ++ faceRows nr.1 i sign)
def checkMargin (nr : ℕ × ℕ) (supports : SupportsCode) : Bool := !badDirection nr supports
def Satisfies (n : ℕ) (rows : List RowCode) (x : Fin n → ℝ) : Prop :=
  ∀ row ∈ rows, (decodeRow n row).eval x ≤ 0
def prependChoices (p : ℕ × List VectorCode) (states : List (List RowCode)) : List (List RowCode) :=
  p.2.flatMap fun u => states.map fun rows => supportRow p.1 u :: rows
end Kourovka.MetabelianEnumeration.ComputableCone


