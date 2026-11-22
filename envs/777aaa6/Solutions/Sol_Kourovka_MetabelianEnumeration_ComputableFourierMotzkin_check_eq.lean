-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.check_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:43.40604+00:00
-- url     : https://prove2.me/submissions/9b015c4d-a677-4420-9557-611bb866b60b

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_decode_eliminate

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
theorem _root_.solution (n : ℕ) (rows : List RowCode) :
    check n rows = FourierMotzkin.check n (rows.map (decodeRow n)) := by
  induction n generalizing rows with
  | zero =>
    rw [Bool.eq_iff_iff]
    simp [check, FourierMotzkin.check, decodeRow, List.all_map, Function.comp_def]
  | succ n ih =>
    rw [check, Function.iterate_succ_apply]
    change check n (eliminate rows) = _
    rw [ih, decode_eliminate, FourierMotzkin.check]
end Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
