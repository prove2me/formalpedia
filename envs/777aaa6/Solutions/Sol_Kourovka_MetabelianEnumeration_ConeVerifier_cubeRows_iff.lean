-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.cubeRows_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:59.343312+00:00
-- url     : https://prove2.me/submissions/876c86e8-8884-4e3b-8f0b-26f7251ed394

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_coordinate_eval

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (x : Fin n → ℝ) :
    Satisfies (cubeRows n) x ↔ ∀ i, -1 ≤ x i ∧ x i ≤ 1 := by
  constructor
  · intro h i
    have hu := h (coordinate i 1 (-1))
      (List.mem_flatMap.mpr ⟨i, by simp, by simp⟩)
    have hl := h (coordinate i (-1) (-1))
      (List.mem_flatMap.mpr ⟨i, by simp, by simp⟩)
    simp only [coordinate_eval, Rat.cast_one, Rat.cast_neg, one_mul, neg_mul] at hu hl
    constructor <;> linarith
  · intro h r hr
    obtain ⟨i, _, hr⟩ := List.mem_flatMap.mp hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      simp only [coordinate_eval, Rat.cast_one, Rat.cast_neg, one_mul, neg_mul] <;>
      obtain ⟨hl, hu⟩ := h i <;> linarith
end Kourovka.MetabelianEnumeration.ConeVerifier
