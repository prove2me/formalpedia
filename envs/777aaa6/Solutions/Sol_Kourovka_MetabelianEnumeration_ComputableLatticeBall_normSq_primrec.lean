-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableLatticeBall.normSq_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:08:33.201033+00:00
-- url     : https://prove2.me/submissions/67f15db8-d0ae-44af-bed0-a005559cd344

import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_nat_sum_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_natAbs_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_nat_pow_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableLatticeBall
open ComputableIntegers ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableLatticeBall
theorem _root_.solution : Primrec normSq :=
  nat_sum_primrec.comp (Primrec.list_map Primrec.id
    (nat_pow_primrec.comp (natAbs_primrec.comp Primrec.snd) (Primrec.const 2)).to₂)
end Kourovka.MetabelianEnumeration.ComputableLatticeBall
