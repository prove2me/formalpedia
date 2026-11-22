-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.checkWord_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:52.605857+00:00
-- url     : https://prove2.me/submissions/d76d4670-1807-47e7-80b6-7ec55b11f0eb

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Kourovka_Certificates_WordCertificates
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_hasDerivation_iff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
theorem _root_.solution {n : ℕ} (rels : List (FreeGroup (Fin n))) (w : Word n) :
    (∃ d, checkWord rels w d = true) ↔
      PresentedGroup.mk {r | r ∈ rels} (FreeGroup.mk w) = 1 := by
  simp only [checkWord, decide_eq_true_eq, PresentedGroup.mk_eq_one_iff]
  exact hasDerivation_iff rels (FreeGroup.mk w)
end Kourovka.MetabelianEnumeration.WordCertificates
