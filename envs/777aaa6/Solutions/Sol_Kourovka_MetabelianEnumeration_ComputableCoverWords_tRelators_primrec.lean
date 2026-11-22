-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverWords.tRelators_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:11:11.993448+00:00
-- url     : https://prove2.me/submissions/a9a12907-ca0e-43d4-a69a-93394aae234b

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_tRelator_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_dimension_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableCoverWords
theorem _root_.solution : Primrec tRelators := by
  have hlt : PrimrecRel (fun j i : ℕ => i < j) :=
    Primrec.nat_lt.comp Primrec.snd Primrec.fst
  have hjs : Primrec (fun p : DatumCode × ℕ =>
      (List.range (dimension p.1)).filter fun j => p.2 < j) :=
    hlt.listFilter.comp
      (Primrec.list_range.comp (dimension_primrec.comp Primrec.fst)) Primrec.snd
  exact Primrec.list_flatMap (Primrec.list_range.comp dimension_primrec)
    (Primrec.list_map hjs
      (tRelator_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂).to₂
end Kourovka.MetabelianEnumeration.ComputableCoverWords
