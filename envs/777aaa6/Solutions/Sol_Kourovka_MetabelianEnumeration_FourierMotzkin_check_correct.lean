-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FourierMotzkin.check_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:26.858434+00:00
-- url     : https://prove2.me/submissions/ea9661a2-b988-45f0-9980-351b33972c6a

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_feasible_eliminate_iff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin
namespace Kourovka.MetabelianEnumeration.FourierMotzkin
theorem _root_.solution (n : ℕ) (rows : List (Row n))
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    check n rows = true ↔ Feasible rows K := by
  induction n with
  | zero =>
    simp only [check, List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨Fin.elim0, ?_⟩
      intro r hr
      have hcast : (r.constant : K) ≤ 0 := by exact_mod_cast h r hr
      simpa [Row.eval] using hcast
    · rintro ⟨x, hx⟩ r hr
      have hcast : (r.constant : K) ≤ 0 := by simpa [Row.eval] using hx r hr
      exact_mod_cast hcast
  | succ n ih =>
    rw [check, ih, feasible_eliminate_iff]
end Kourovka.MetabelianEnumeration.FourierMotzkin
