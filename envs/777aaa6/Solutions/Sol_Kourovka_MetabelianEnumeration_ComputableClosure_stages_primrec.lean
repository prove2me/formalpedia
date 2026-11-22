-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableClosure.stages_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:54.344151+00:00
-- url     : https://prove2.me/submissions/e7bd6458-b1fe-4c0b-92b3-1aa5771e3c1a

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_expand_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv
omit [DecidableEq G]
namespace Kourovka.MetabelianEnumeration.ComputableClosure
theorem _root_.solution : Primrec (fun p : (List G × List G) × ℕ => stages p.1.1 p.1.2 p.2) :=
  Primrec.nat_iterate Primrec.snd
    (Primrec.list_cons.comp (Primrec.const 1) (Primrec.fst.comp Primrec.fst))
    ((expand_primrec hmul hinv).comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂
end Kourovka.MetabelianEnumeration.ComputableClosure
