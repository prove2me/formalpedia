-- Prove2me | Definitions.Def_Kourovka_Covers_CoverMargin
-- name    : Kourovka_Covers_CoverMargin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:44:54.769182+00:00
-- url     : https://prove2.me/theorems/7828cf38-6683-4be4-8307-f40eadc6c251
-- title:
--   Cover Margin
-- statement:
--   Definitions and structural lemmas for Cover Margin, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverMargin.lean

import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Modules_TamenessCompactness
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.FiniteCover
open Collection ConeVerifier TamenessCompactness
def supportLength {k : ℕ} (v : Lattice k) : ℚ := ∑ i, |(v i : ℚ)|
def supportLengths {k a : ℕ} (data : Datum k a) : List ℚ :=
  data.polynomials.flatMap fun p => p.2.map fun term => supportLength term.1
def supportBound {k a : ℕ} (data : Datum k a) : ℚ := 1 + (supportLengths data).sum
end Kourovka.MetabelianEnumeration.FiniteCover


