-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableClosure.presented_word_problem_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:09.314952+00:00
-- url     : https://prove2.me/submissions/81373604-c7f4-4461-99a3-e082a50ffeef

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_normalClosure_re
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_inv_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mul_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.ComputableClosure
theorem _root_.solution {α : Type*} [Primcodable α] [DecidableEq α] :
    REPred (fun input : List (FreeGroup α) × FreeGroup α =>
      PresentedGroup.mk {r | r ∈ input.1} input.2 = 1) := by
  apply (normalClosure_re ComputableWords.mul_primrec ComputableWords.inv_primrec).of_eq
  intro input
  exact PresentedGroup.mk_eq_one_iff.symm
end Kourovka.MetabelianEnumeration.ComputableClosure
