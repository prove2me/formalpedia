-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.supportLengths_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:07:26.94071+00:00
-- url     : https://prove2.me/submissions/d4927a18-3063-4dac-b073-0a49b6025fbf

import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverMargin
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_supportLength_nonneg

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection ConeVerifier TamenessCompactness
namespace Kourovka.MetabelianEnumeration.FiniteCover
theorem _root_.solution {k a : ℕ} (data : Datum k a) :
    ∀ x ∈ supportLengths data, 0 ≤ x := by
  intro x hx
  obtain ⟨p, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨term, _, rfl⟩ := List.mem_map.mp hx
  exact supportLength_nonneg term.1
end Kourovka.MetabelianEnumeration.FiniteCover
