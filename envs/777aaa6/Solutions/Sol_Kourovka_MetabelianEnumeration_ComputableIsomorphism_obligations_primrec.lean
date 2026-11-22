-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.obligations_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:53:15.945367+00:00
-- url     : https://prove2.me/submissions/c7b64a31-9383-4d31-b2e4-543090dfae20

import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_relatorChecks_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_inverseChecks_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution : Primrec obligations := by
  let p : Primrec (fun d : MapInput => d.1.1) := Primrec.fst.comp Primrec.fst
  let q : Primrec (fun d : MapInput => d.1.2) := Primrec.snd.comp Primrec.fst
  let f : Primrec (fun d : MapInput => d.2.1) := Primrec.fst.comp Primrec.snd
  let g : Primrec (fun d : MapInput => d.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp
    (relatorChecks_primrec.comp (p.pair (q.pair f)))
    (relatorChecks_primrec.comp (q.pair (p.pair g))))
    (inverseChecks_primrec.comp (p.pair (f.pair g))))
    (inverseChecks_primrec.comp (q.pair (g.pair f)))
end Kourovka.MetabelianEnumeration.ComputableIsomorphism
