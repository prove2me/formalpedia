-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.decode_eliminate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:41.669972+00:00
-- url     : https://prove2.me/submissions/8daa9885-d059-41f1-aa6c-fe80af32ed79

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_decode_head
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_decode_tail
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_decode_combine
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_map_filter_eq

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
theorem _root_.solution (n : ℕ) (rows : List RowCode) :
    (eliminate rows).map (decodeRow n) =
      FourierMotzkin.eliminate (rows.map (decodeRow (n + 1))) := by
  have hz : ((rows.filter fun r => head r = 0).map (decodeRow (n + 1))) =
      (rows.map (decodeRow (n + 1))).filter (fun r => r.head = 0) := by
    apply map_filter_eq
    intro r; norm_cast; simp [decode_head] <;> norm_cast
  have hn : ((rows.filter fun r => head r < 0).map (decodeRow (n + 1))) =
      FourierMotzkin.negatives (rows.map (decodeRow (n + 1))) := by
    apply map_filter_eq
    intro r; norm_cast; simp [decode_head] <;> norm_cast
  have hp : ((rows.filter fun r => 0 < head r).map (decodeRow (n + 1))) =
      FourierMotzkin.positives (rows.map (decodeRow (n + 1))) := by
    apply map_filter_eq
    intro r; norm_cast; simp [decode_head] <;> norm_cast
  simp only [eliminate, List.map_append, List.map_map, List.map_flatMap,
    FourierMotzkin.eliminate, ← hz, ← hn, ← hp, List.map_map, List.flatMap_map]
  simp only [Function.comp_def, decode_tail, decode_combine]
end Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
