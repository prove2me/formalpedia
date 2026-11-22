-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputablePresentations.wellFormed_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:44:51.683536+00:00
-- url     : https://prove2.me/submissions/b030a903-2549-4e05-98a6-bbcadc24ef9e

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords
namespace Kourovka.MetabelianEnumeration.ComputablePresentations
theorem _root_.solution : PrimrecPred WellFormed := by
  have hletter : PrimrecRel (fun letter : ℕ × Bool => fun n => letter.1 < n) :=
    Primrec.nat_lt.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact hletter.forall_mem_list.forall_mem_list.comp Primrec.snd Primrec.fst
end Kourovka.MetabelianEnumeration.ComputablePresentations
