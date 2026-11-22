-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.completion_of_certificates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:34.20387+00:00
-- url     : https://prove2.me/submissions/689b6c7a-b726-4328-8bb5-26eb82767a6f

import Definitions.Def_Kourovka_Computability_Enumeration
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Commutator.Basic
import Definitions.Def_Kourovka_Presentations_Presentations
import Theorems.Thm_Kourovka_MetabelianEnumeration_recursively_enumerable_of_certificates


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration
namespace Kourovka.MetabelianEnumeration
theorem _root_.solution
    (check : ℕ → ℕ → Bool) (hc : Computable₂ check)
    (correct : ∀ p, DefinesMetabelian p ↔ ∃ c, check p c = true) : MainClaim :=
  recursively_enumerable_of_certificates check hc DefinesMetabelian correct
end Kourovka.MetabelianEnumeration
