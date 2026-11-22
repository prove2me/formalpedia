-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.validMaps_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:51:26.002999+00:00
-- url     : https://prove2.me/submissions/779b082e-7802-4667-b316-e0d655b8f2b1

import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_wellFormed_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution : PrimrecPred validMaps := by
  let p : Primrec (fun d : MapInput => d.1.1) := Primrec.fst.comp Primrec.fst
  let q : Primrec (fun d : MapInput => d.1.2) := Primrec.snd.comp Primrec.fst
  let f : Primrec (fun d : MapInput => d.2.1) := Primrec.fst.comp Primrec.snd
  let g : Primrec (fun d : MapInput => d.2.2) := Primrec.snd.comp Primrec.snd
  exact (wellFormed_primrec.comp p).and ((wellFormed_primrec.comp q).and
    ((Primrec.eq.comp (Primrec.list_length.comp f) (Primrec.fst.comp p)).and
      ((Primrec.eq.comp (Primrec.list_length.comp g) (Primrec.fst.comp q)).and
        ((wellFormed_primrec.comp ((Primrec.fst.comp q).pair f)).and
          (wellFormed_primrec.comp ((Primrec.fst.comp p).pair g))))))
end Kourovka.MetabelianEnumeration.ComputableIsomorphism
