-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableClosure.check_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:17.085186+00:00
-- url     : https://prove2.me/submissions/e1351710-5e08-4f0d-8606-b6103a0a38e5

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_stages_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv
namespace Kourovka.MetabelianEnumeration.ComputableClosure
theorem _root_.solution : Primrec₂ (@check G _ _) := by
  have hm : PrimrecRel (fun xs : List G => fun x => x ∈ xs) :=
    Primrec.eq.exists_mem_list.of_eq (fun p => by simp)
  exact hm.decide.comp
    ((stages_primrec hmul hinv).comp
      (((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd))) (Primrec.snd.comp Primrec.fst)
end Kourovka.MetabelianEnumeration.ComputableClosure
