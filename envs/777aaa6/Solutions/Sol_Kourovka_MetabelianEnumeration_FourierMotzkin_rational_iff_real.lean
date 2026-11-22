-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FourierMotzkin.rational_iff_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:40.998968+00:00
-- url     : https://prove2.me/submissions/f958e5a2-f7d8-484f-a09b-9c06999ae12b

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_check_correct

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin
namespace Kourovka.MetabelianEnumeration.FourierMotzkin
theorem _root_.solution {n : ℕ} (rows : List (Row n)) :
    Feasible rows ℚ ↔ Feasible rows ℝ :=
  (check_correct n rows ℚ).symm.trans (check_correct n rows ℝ)
end Kourovka.MetabelianEnumeration.FourierMotzkin
