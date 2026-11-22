-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.hasDerivation_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:45.951841+00:00
-- url     : https://prove2.me/submissions/176fb836-c27f-4dac-833f-739928e3ec82

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Kourovka_Certificates_WordCertificates
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_Derivation_eval_mem
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_normalClosure_le_derivable

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
theorem _root_.solution {n : ℕ} (rels : List (FreeGroup (Fin n)))
    (r : FreeGroup (Fin n)) :
    (∃ d : Derivation n, d.eval rels = r) ↔ r ∈ Subgroup.normalClosure {r | r ∈ rels} := by
  constructor
  · rintro ⟨d, rfl⟩
    exact d.eval_mem rels
  · intro h
    exact normalClosure_le_derivable rels h
end Kourovka.MetabelianEnumeration.WordCertificates
