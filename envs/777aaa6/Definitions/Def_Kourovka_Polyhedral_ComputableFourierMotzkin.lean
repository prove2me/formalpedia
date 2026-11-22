-- Prove2me | Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
-- name    : Kourovka_Polyhedral_ComputableFourierMotzkin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:43:43.943167+00:00
-- url     : https://prove2.me/theorems/608beccb-1604-45d5-bcd2-722cb176291f
-- title:
--   Computable Fourier Motzkin
-- statement:
--   Definitions and structural lemmas for Computable Fourier Motzkin, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers
abbrev RowCode := List ℤ × ℤ
def coeff (r : RowCode) (i : ℕ) : ℤ := r.1.getD i 0
def head (r : RowCode) : ℤ := coeff r 0
def tail (r : RowCode) : RowCode := (r.1.tail, r.2)
def combineCoeff (p : RowCode × RowCode) (i : ℕ) : ℤ :=
  head p.2 * coeff p.1 i - head p.1 * coeff p.2 i
def combine (p : RowCode × RowCode) : RowCode :=
  ((List.range (max p.1.1.length p.2.1.length)).map fun i => combineCoeff p (i + 1),
    head p.2 * p.1.2 - head p.1 * p.2.2)
def eliminate (rows : List RowCode) : List RowCode :=
  (rows.filter (fun r => head r = 0)).map tail ++
    (rows.filter (fun r => head r < 0)).flatMap fun l =>
      (rows.filter (fun r => 0 < head r)).map fun u => combine (l, u)
def check (n : ℕ) (rows : List RowCode) : Bool :=
  ((eliminate^[n]) rows).all fun r => r.2 ≤ 0
def decodeRow (n : ℕ) (r : RowCode) : FourierMotzkin.Row n :=
  ⟨fun i => (coeff r i : ℚ), r.2⟩
end Kourovka.MetabelianEnumeration.ComputableFourierMotzkin


