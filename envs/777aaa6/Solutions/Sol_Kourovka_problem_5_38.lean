-- Prove2me | solution 1 for Kourovka.problem_5_38
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:48:26.440328+00:00
-- url     : https://prove2.me/submissions/ba612d8b-02fc-4cf3-9f54-f71a2b9285c3

import Definitions.Def_Kourovka_CentralHopfian
import Definitions.Def_Kourovka_QuotientProducts
import Definitions.Def_Kourovka_Problem
import Definitions.Def_Kourovka_Paper
import Theorems.Thm_Kourovka_directProduct_isHopfian


set_option autoImplicit true
open Kourovka
namespace Kourovka
theorem _root_.solution (A B : Type*) [Group A] [Group B] : ProductHopficityStatement A B := by
  intro hfgA hfgB hsolA hsolB hhopA hhopB
  letI : Group.FG A := hfgA
  letI : Group.FG B := hfgB
  letI : IsSolvable A := hsolA
  letI : IsSolvable B := hsolB
  exact directProduct_isHopfian hhopA hhopB
end Kourovka
