-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.relatorChecks_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:52:16.534168+00:00
-- url     : https://prove2.me/submissions/24644610-0932-4b78-b20c-6b7b531c32db

import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_substitute_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution : Primrec relatorChecks :=
  Primrec.list_map (Primrec.snd.comp Primrec.fst)
    (((Primrec.fst.comp Primrec.snd).comp Primrec.fst).pair
      (substitute_primrec.comp ((Primrec.snd.comp Primrec.snd).comp Primrec.fst)
        Primrec.snd)).to₂
end Kourovka.MetabelianEnumeration.ComputableIsomorphism
