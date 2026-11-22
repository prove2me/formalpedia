-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.normalClosure_le_derivable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:59:56.133448+00:00
-- url     : https://prove2.me/submissions/2bcb5360-742b-46a8-a715-05a9b4a48e69

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Kourovka_Certificates_WordCertificates

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
theorem _root_.solution {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    Subgroup.normalClosure {r | r ∈ rels} ≤ derivableSubgroup rels := by
  apply Subgroup.normalClosure_le_normal
  intro r hr
  change r ∈ rels at hr
  refine ⟨.relator r.toWord, ?_⟩
  simp only [Derivation.eval, FreeGroup.mk_toWord, if_pos hr]
end Kourovka.MetabelianEnumeration.WordCertificates
