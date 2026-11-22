-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.decode_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:44.751065+00:00
-- url     : https://prove2.me/submissions/248c0988-b495-4c9a-baf1-15b8999b6af8

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
theorem _root_.solution (n : ℕ) (r : RowCode) : (decodeRow (n + 1) r).head = (head r : ℚ) := rfl
end Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
