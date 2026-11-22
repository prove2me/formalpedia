-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableClosure.check_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:39.460757+00:00
-- url     : https://prove2.me/submissions/1f5d25b2-0f3e-4c8f-bfa4-11e0108b362e

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_mem_normalClosure_iff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv
omit hmul hinv [Primcodable G]
namespace Kourovka.MetabelianEnumeration.ComputableClosure
theorem _root_.solution (input : List G × G) :
    (∃ certificate, check input certificate = true) ↔
      input.2 ∈ Subgroup.normalClosure {r | r ∈ input.1} := by
  simp only [check, decide_eq_true_eq, Prod.exists]
  exact (mem_normalClosure_iff _ _).symm
end Kourovka.MetabelianEnumeration.ComputableClosure
