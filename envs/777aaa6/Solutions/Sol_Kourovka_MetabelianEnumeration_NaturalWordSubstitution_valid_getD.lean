-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.NaturalWordSubstitution.valid_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:45:06.365571+00:00
-- url     : https://prove2.me/submissions/efb02f0d-def2-4be5-9f08-99037fc5ffba

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations
namespace Kourovka.MetabelianEnumeration.NaturalWordSubstitution
theorem _root_.solution (n : ℕ) (f : Images) (hf : WellFormed (n, f)) (i : ℕ) :
    ValidWord n (f.getD i []) := by
  by_cases hi : i < f.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hf _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    intro z hz
    exact False.elim (List.not_mem_nil hz)
end Kourovka.MetabelianEnumeration.NaturalWordSubstitution
