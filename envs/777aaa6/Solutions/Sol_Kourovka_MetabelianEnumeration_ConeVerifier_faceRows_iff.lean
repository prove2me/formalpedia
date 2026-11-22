-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.faceRows_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:46.316174+00:00
-- url     : https://prove2.me/submissions/25d35fc3-6561-43b9-80b4-d9c830930a6e

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_coordinate_eval
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_cubeRows_iff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (i : Fin n) (sign : ℚ) (x : Fin n → ℝ) :
    Satisfies (faceRows i sign) x ↔ x i = sign ∧ ∀ j, -1 ≤ x j ∧ x j ≤ 1 := by
  constructor
  · intro h
    have hu := h (coordinate i 1 (-sign)) (by simp [faceRows])
    have hl := h (coordinate i (-1) sign) (by simp [faceRows])
    simp only [coordinate_eval, Rat.cast_one, Rat.cast_neg, one_mul, neg_mul] at hu hl
    exact ⟨by linarith, (cubeRows_iff x).mp (fun r hr => h r (by simp [faceRows, hr]))⟩
  · rintro ⟨hi, hcube⟩ r hr
    simp only [faceRows, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | hr
    · simp [coordinate_eval, hi]
    · simp [coordinate_eval, hi]
    · exact (cubeRows_iff x).mpr hcube r hr
end Kourovka.MetabelianEnumeration.ConeVerifier
