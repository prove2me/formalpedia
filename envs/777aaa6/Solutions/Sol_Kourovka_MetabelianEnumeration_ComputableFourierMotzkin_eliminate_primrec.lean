-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.eliminate_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:07:57.231355+00:00
-- url     : https://prove2.me/submissions/aceb69ef-09b1-4ca6-9830-597fbbb922d2

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_head_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_tail_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_combine_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_lt_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
theorem _root_.solution : Primrec eliminate := by
  have hz : Primrec (fun rows : List RowCode => rows.filter fun r => head r = 0) :=
    Primrec.listFilter (Primrec.eq.comp head_primrec (Primrec.const 0))
  have hn : Primrec (fun rows : List RowCode => rows.filter fun r => head r < 0) :=
    Primrec.listFilter (lt_primrec.comp head_primrec (Primrec.const 0))
  have hp : Primrec (fun rows : List RowCode => rows.filter fun r => 0 < head r) :=
    Primrec.listFilter (lt_primrec.comp (Primrec.const 0) head_primrec)
  exact Primrec.list_append.comp
    (Primrec.list_map hz (tail_primrec.comp Primrec.snd).to₂)
    (Primrec.list_flatMap hn
      (Primrec.list_map (hp.comp Primrec.fst)
        (combine_primrec.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).to₂)
end Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
