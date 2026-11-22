-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableEpimorphism.obligations_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:46.527242+00:00
-- url     : https://prove2.me/submissions/afef2430-df5c-4a10-9eb4-48f00aa43cab

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_inverseChecks_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_relatorChecks_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableEpimorphism
theorem _root_.solution : Primrec obligations := by
  let p : Primrec (fun d : MapInput => d.1.1) := Primrec.fst.comp Primrec.fst
  let q : Primrec (fun d : MapInput => d.1.2) := Primrec.snd.comp Primrec.fst
  let f : Primrec (fun d : MapInput => d.2.1) := Primrec.fst.comp Primrec.snd
  let g : Primrec (fun d : MapInput => d.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_append.comp
    (ComputableIsomorphism.relatorChecks_primrec.comp (p.pair (q.pair f)))
    (ComputableIsomorphism.inverseChecks_primrec.comp (q.pair (g.pair f)))
end Kourovka.MetabelianEnumeration.ComputableEpimorphism
