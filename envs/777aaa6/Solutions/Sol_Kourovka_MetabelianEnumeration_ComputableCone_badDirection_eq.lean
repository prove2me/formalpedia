-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.badDirection_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:06:58.542223+00:00
-- url     : https://prove2.me/submissions/149b2541-3015-49be-90f1-68b1fb643b21

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_check_face_correct
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_badDirection_correct


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution (nr : ℕ × ℕ) (supports : SupportsCode) :
    badDirection nr supports =
      ConeVerifier.badDirection (decodeSupports nr.1 supports) ((1 / 2 : ℚ) ^ nr.2) := by
  rw [Bool.eq_iff_iff, ConeVerifier.badDirection_correct]
  simp only [badDirection, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi, sign, hsign, h⟩
    obtain ⟨x, hface, hs⟩ := (check_face_correct nr.1 nr.2 supports ⟨i, hi⟩ sign).mp (List.any_eq_true.mpr h)
    refine ⟨x, ⟨hface.2, ⟨i, hi⟩, ?_⟩, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hsign
      rcases hsign with rfl | rfl <;> simp_all
    · intro support hsupport
      obtain ⟨s, hsmem, rfl⟩ := List.mem_map.mp hsupport
      obtain ⟨u, hu, hux⟩ := hs s hsmem
      exact ⟨decodeVector nr.1 u, List.mem_map.mpr ⟨u, hu, rfl⟩, by simpa using hux⟩
  · rintro ⟨x, ⟨hcube, i, hi⟩, hs⟩
    have hs' : ∀ support ∈ supports, ∃ u ∈ support,
        ConeVerifier.dot (decodeVector nr.1 u) x ≤ (1 / 2 : ℝ) ^ nr.2 := by
      intro support hsupport
      obtain ⟨u, hu, hux⟩ := hs (support.map (decodeVector nr.1))
        (List.mem_map.mpr ⟨support, hsupport, rfl⟩)
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
      exact ⟨v, hv, by simpa using hux⟩
    rcases hi with hi | hi
    · refine ⟨i, i.isLt, -1, by simp, ?_⟩
      exact List.any_eq_true.mp ((check_face_correct _ _ _ i (-1)).mpr ⟨x, ⟨by simpa using hi, hcube⟩, hs'⟩)
    · refine ⟨i, i.isLt, 1, by simp, ?_⟩
      exact List.any_eq_true.mp ((check_face_correct _ _ _ i 1).mpr ⟨x, ⟨by simpa using hi, hcube⟩, hs'⟩)
end Kourovka.MetabelianEnumeration.ComputableCone
