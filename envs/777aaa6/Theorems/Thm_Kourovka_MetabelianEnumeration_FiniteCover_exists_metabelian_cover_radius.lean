-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_exists_metabelian_cover_radius
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.exists_metabelian_cover_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:07:39.81054+00:00
-- url     : https://prove2.me/theorems/d687264e-0bab-4ee7-afcc-dcbb7a4379e2
-- title:
--   Finite Cover: exists metabelian cover radius
-- statement:
--   Every finite cone cover has an explicit integer radius at which its
--   ordinary finite group presentation is metabelian.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CertifiedCover.lean#L46-L50
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CertifiedCover.lean#L46-L50

import Definitions.Def_Kourovka_Covers_CoverSoundness
import Definitions.Def_Kourovka_Covers_CoverMargin
import Definitions.Def_Kourovka_Covers_CertifiedCover
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection ConeVerifier TamenessCompactness

theorem Kourovka.MetabelianEnumeration.FiniteCover.exists_metabelian_cover_radius {k a : ℕ} (data : Datum k a) (hk : 1 ≤ k)
    (hc : ConeCover (data.polynomials.map polynomialSupport)) :
    ∃ R : ℕ, Metabelian (GroupOf data R) := by sorry
