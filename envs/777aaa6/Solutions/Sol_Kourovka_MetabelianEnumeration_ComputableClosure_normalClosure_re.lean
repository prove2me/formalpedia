-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableClosure.normalClosure_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:41.202994+00:00
-- url     : https://prove2.me/submissions/2928db68-175f-4beb-9c11-f91f6ec290ca

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_checkNat_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_checkNat_correct

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv
namespace Kourovka.MetabelianEnumeration.ComputableClosure
theorem _root_.solution :
    REPred (fun input : List G × G => input.2 ∈ Subgroup.normalClosure {r | r ∈ input.1}) := by
  have hp : Partrec (fun input : List G × G =>
      Nat.rfind (fun c => (checkNat input c : Part Bool))) :=
    Partrec.rfind (checkNat_primrec hmul hinv).to_comp.partrec.to₂
  apply hp.dom_re.of_eq
  intro input
  rw [Nat.rfind_dom, ← checkNat_correct]
  simp
end Kourovka.MetabelianEnumeration.ComputableClosure
