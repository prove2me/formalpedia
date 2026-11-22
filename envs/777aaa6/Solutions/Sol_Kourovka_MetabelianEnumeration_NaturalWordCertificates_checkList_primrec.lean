-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.NaturalWordCertificates.checkList_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:43.008097+00:00
-- url     : https://prove2.me/submissions/40f2a754-a8fb-4ada-a928-33756d8622d2

import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_checkTrivial_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordCertificates
open ComputablePresentations NaturalWordSubstitution
namespace Kourovka.MetabelianEnumeration.NaturalWordCertificates
theorem _root_.solution : Primrec₂ checkList := by
  have hinput : Primrec (fun p : ℕ × (List Input × List ℕ) => p.2.1.getD p.1 ((0, []), [])) :=
    (Primrec.list_getD ((0, []), [])).comp (Primrec.fst.comp Primrec.snd) Primrec.fst
  have hcert : Primrec (fun p : ℕ × (List Input × List ℕ) => p.2.2.getD p.1 0) :=
    (Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  have hrel : PrimrecRel (fun i : ℕ => fun p : List Input × List ℕ =>
      checkTrivial (p.1.getD i ((0, []), [])) (p.2.getD i 0) = true) :=
    Primrec.eq.comp (checkTrivial_primrec.comp hinput hcert) (Primrec.const true)
  exact (hrel.forall_mem_list.comp
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) Primrec.id).decide
end Kourovka.MetabelianEnumeration.NaturalWordCertificates
