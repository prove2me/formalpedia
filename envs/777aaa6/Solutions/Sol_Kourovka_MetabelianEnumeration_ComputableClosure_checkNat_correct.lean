-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableClosure.checkNat_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:38.667399+00:00
-- url     : https://prove2.me/submissions/599745fc-ec64-4d7e-9b1a-3feef3f8bd1a

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_correct

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv
omit hmul hinv
namespace Kourovka.MetabelianEnumeration.ComputableClosure
theorem _root_.solution (input : List G × G) :
    (∃ certificate, checkNat input certificate = true) ↔
      input.2 ∈ Subgroup.normalClosure {r | r ∈ input.1} := by
  rw [← check_correct]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨_, hn⟩
  · rintro ⟨certificate, hc⟩
    refine ⟨Encodable.encode certificate, ?_⟩
    simpa [checkNat] using hc
end Kourovka.MetabelianEnumeration.ComputableClosure
