-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputablePresentations.validInput_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:16.750304+00:00
-- url     : https://prove2.me/submissions/bfc98a3d-b212-4540-9a64-52f026d1ba40

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_wellFormed_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords
namespace Kourovka.MetabelianEnumeration.ComputablePresentations
theorem _root_.solution : PrimrecPred validInput := by
  have hletter : PrimrecRel (fun letter : ℕ × Bool => fun n => letter.1 < n) :=
    Primrec.nat_lt.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact (wellFormed_primrec.comp Primrec.fst).and
    (hletter.forall_mem_list.comp Primrec.snd (Primrec.fst.comp Primrec.fst))
end Kourovka.MetabelianEnumeration.ComputablePresentations
