-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.inverseChecks_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:52:17.175269+00:00
-- url     : https://prove2.me/submissions/f50f6665-4a20-417b-ade4-785bc3afd80a

import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_substitute_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution : Primrec inverseChecks := by
  have hf : Primrec (fun d : (PresentationCode × Maps) × ℕ => d.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hg : Primrec (fun d : (PresentationCode × Maps) × ℕ => d.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hword := substitute_primrec.comp hg ((Primrec.list_getD []).comp hf Primrec.snd)
  have hletter : Primrec (fun d : (PresentationCode × Maps) × ℕ => [(d.2, false)]) :=
    Primrec.list_cons.comp (Primrec.snd.pair (Primrec.const false)) (Primrec.const [])
  exact Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst))
    (((Primrec.fst.comp Primrec.fst).pair (Primrec.list_append.comp hword hletter)).to₂)
end Kourovka.MetabelianEnumeration.ComputableIsomorphism
