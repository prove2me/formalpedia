-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.check_face_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:58.720176+00:00
-- url     : https://prove2.me/submissions/3042af28-7f4e-438c-b0a5-a8094397192c

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_decode_faceRows
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_satisfies_decode
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_choices_correct
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_correct
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_check_eq
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_faceRows_iff
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_check_correct


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution (n r : ℕ) (supports : SupportsCode) (i : Fin n) (sign : ℤ) :
    ((choices r supports).any fun rows =>
      ComputableFourierMotzkin.check n (rows ++ faceRows n i sign)) = true ↔
    ∃ x : Fin n → ℝ, (x i = (sign : ℝ) ∧ ∀ j, -1 ≤ x j ∧ x j ≤ 1) ∧
      ∀ support ∈ supports, ∃ u ∈ support,
        ConeVerifier.dot (decodeVector n u) x ≤ (1 / 2 : ℝ) ^ r := by
  simp only [List.any_eq_true, ComputableFourierMotzkin.check_eq,
    FourierMotzkin.check_correct n _ ℝ, FourierMotzkin.Feasible]
  constructor
  · rintro ⟨rows, hrows, x, hx⟩
    have hface : FourierMotzkin.Satisfies (ConeVerifier.faceRows i (sign : ℚ)) x := by
      rw [← decode_faceRows]
      intro row hrow
      exact hx row (by simpa only [List.map_append, List.mem_append] using Or.inr hrow)
    have hsat : Satisfies n rows x := by
      apply (satisfies_decode _ _ _).mp
      intro row hrow
      exact hx row (by simpa only [List.map_append, List.mem_append] using Or.inl hrow)
    refine ⟨x, ?_, (choices_correct n r supports x).mp ⟨rows, hrows, hsat⟩⟩
    simpa using (ConeVerifier.faceRows_iff i (sign : ℚ) x).mp hface
  · rintro ⟨x, hface, hs⟩
    obtain ⟨rows, hrows, hsat⟩ := (choices_correct n r supports x).mpr hs
    refine ⟨rows, hrows, x, ?_⟩
    have hf : FourierMotzkin.Satisfies (ConeVerifier.faceRows i (sign : ℚ)) x :=
      (ConeVerifier.faceRows_iff i (sign : ℚ) x).mpr (by simpa using hface)
    intro row hrow
    rw [List.map_append, List.mem_append] at hrow
    rcases hrow with hrow | hrow
    · exact (satisfies_decode _ _ _).mpr hsat row hrow
    · rw [decode_faceRows] at hrow
      exact hf row hrow
end Kourovka.MetabelianEnumeration.ComputableCone
