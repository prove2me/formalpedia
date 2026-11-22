-- Prove2me | Definitions.Def_Kourovka_Modules_TamenessCompactness
-- name    : Kourovka_Modules_TamenessCompactness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:43:27.501879+00:00
-- url     : https://prove2.me/theorems/9aed4439-438d-4510-a3cb-dc1f1a833a9d
-- title:
--   Tameness Compactness
-- statement:
--   Definitions and structural lemmas for Tameness Compactness, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/TamenessCompactness.lean

import Definitions.Def_Kourovka_Covers_FiniteCover
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.TamenessCompactness
open ConeVerifier FiniteCover
def polynomialSupport {k : ℕ} (p : Polynomial k) : List (Vec k) :=
  p.2.map fun term => fun i => (term.1 i : ℚ)
end Kourovka.MetabelianEnumeration.TamenessCompactness


