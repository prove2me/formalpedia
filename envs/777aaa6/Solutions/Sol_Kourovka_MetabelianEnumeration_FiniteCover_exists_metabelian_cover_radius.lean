-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.exists_metabelian_cover_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:20:15.485469+00:00
-- url     : https://prove2.me/submissions/00a83f46-bd7b-4ec8-b3bb-dc8adcd488e1

import Definitions.Def_Kourovka_Covers_CoverSoundness
import Definitions.Def_Kourovka_Covers_CoverMargin
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_checked_cover_metabelian
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_dyadic_margin_search_terminates


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection ConeVerifier TamenessCompactness
namespace Kourovka.MetabelianEnumeration.FiniteCover
theorem _root_.solution {k a : ℕ} (data : Datum k a) (hk : 1 ≤ k)
    (hc : ConeCover (data.polynomials.map polynomialSupport)) :
    ∃ R : ℕ, Metabelian (GroupOf data R) := by
  obtain ⟨r, hr⟩ := dyadic_margin_search_terminates _ hc
  exact ⟨coneRadius data r, checked_cover_metabelian data hk r hr⟩
end Kourovka.MetabelianEnumeration.FiniteCover
