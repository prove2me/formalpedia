-- Prove2me | Definitions.Def_Kourovka_Covers_CertifiedRadius
-- name    : Kourovka_Covers_CertifiedRadius
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:42:45.67864+00:00
-- url     : https://prove2.me/theorems/c1fe21fb-1ed0-43d4-af5a-cf7d89d6fe94
-- title:
--   Certified Radius
-- statement:
--   Definitions and structural lemmas for Certified Radius, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CertifiedRadius.lean

import Definitions.Def_Kourovka_Polyhedral_Radius
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.FiniteCover
def certifiedRadius (k : ℕ) (C D : ℚ) : ℕ :=
  1 + ⌈2 * (k : ℚ) * (1 + D + D ^ 2 / C)⌉₊
def certifiedDelta (k : ℕ) (C : ℚ) : ℚ := min (C / 4) (1 / (4 * (k : ℚ)))
end Kourovka.MetabelianEnumeration.FiniteCover


