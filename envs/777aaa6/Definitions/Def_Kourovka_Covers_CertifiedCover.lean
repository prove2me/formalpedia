-- Prove2me | Definitions.Def_Kourovka_Covers_CertifiedCover
-- name    : Kourovka_Covers_CertifiedCover
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:46:02.70195+00:00
-- url     : https://prove2.me/theorems/40b0fb38-e246-445a-9dbf-e33489756e15
-- title:
--   Certified Cover
-- statement:
--   Definitions and structural lemmas for Certified Cover, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CertifiedCover.lean

import Definitions.Def_Kourovka_Covers_CoverSoundness
import Definitions.Def_Kourovka_Covers_CoverMargin
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.FiniteCover
open Collection ConeVerifier TamenessCompactness
def marginConstant (k r : ℕ) : ℚ := min ((1 / 2 : ℚ) ^ r / k) 1
def coneRadius {k a : ℕ} (data : Datum k a) (r : ℕ) : ℕ :=
  certifiedRadius k (marginConstant k r) (supportBound data)
end Kourovka.MetabelianEnumeration.FiniteCover


