-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.check_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:08:54.858847+00:00
-- url     : https://prove2.me/submissions/e7917b09-e089-42ae-804a-07e824afc4d7

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_eliminate_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_le_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
theorem _root_.solution : Primrec₂ check := by
  have hi : Primrec (fun p : ℕ × List RowCode => (eliminate^[p.1]) p.2) :=
    Primrec.nat_iterate Primrec.fst Primrec.snd (eliminate_primrec.comp Primrec.snd).to₂
  have hall : Primrec (fun rows : List RowCode => rows.all fun r => r.2 ≤ 0) := by
    exact ((le_primrec.comp Primrec.snd (Primrec.const 0)).forall_mem_list.decide).of_eq
      (fun rows => by rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, List.all_eq_true])
  exact hall.comp hi
end Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
