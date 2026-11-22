-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableLatticeBall.ball_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:58.047694+00:00
-- url     : https://prove2.me/submissions/c0213126-f94d-4e71-a1ed-9e4aac8cc312

import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_cube_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_normSq_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_nat_pow_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableLatticeBall
open ComputableIntegers ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableLatticeBall
theorem _root_.solution : Primrec₂ ball := by
  have hp : PrimrecRel (fun v : List ℤ => fun R : ℕ => normSq v < R ^ 2) :=
    Primrec.nat_lt.comp (normSq_primrec.comp Primrec.fst)
      (nat_pow_primrec.comp Primrec.snd (Primrec.const 2))
  exact hp.listFilter.comp (cube_primrec.comp Primrec.snd Primrec.fst) Primrec.snd
end Kourovka.MetabelianEnumeration.ComputableLatticeBall
