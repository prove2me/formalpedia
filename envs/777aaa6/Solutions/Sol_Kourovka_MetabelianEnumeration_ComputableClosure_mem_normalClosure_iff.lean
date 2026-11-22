-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableClosure.mem_normalClosure_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:49.62909+00:00
-- url     : https://prove2.me/submissions/03a6cfbf-42b9-4e19-8205-b65e50aec663

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_stages_sound

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.ComputableClosure
theorem _root_.solution (rels : List G) (x : G) :
    x ∈ Subgroup.normalClosure {r | r ∈ rels} ↔ ∃ C n, x ∈ stages rels C n := by
  constructor
  · apply Subgroup.normalClosure_le_normal (N := reachable rels)
    intro r hr
    exact ⟨[], 0, List.mem_cons_of_mem _ hr⟩
  · rintro ⟨C, n, hx⟩
    exact stages_sound rels C n hx
end Kourovka.MetabelianEnumeration.ComputableClosure
