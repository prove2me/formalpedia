-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableClosure.checkNat_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:06.033086+00:00
-- url     : https://prove2.me/submissions/03e5f705-1452-4715-883d-f4475d091a9a

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv
namespace Kourovka.MetabelianEnumeration.ComputableClosure
theorem _root_.solution : Primrec₂ (@checkNat G _ _ _) :=
  (check_primrec hmul hinv).comp Primrec.fst
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const ([], 0)))
end Kourovka.MetabelianEnumeration.ComputableClosure
