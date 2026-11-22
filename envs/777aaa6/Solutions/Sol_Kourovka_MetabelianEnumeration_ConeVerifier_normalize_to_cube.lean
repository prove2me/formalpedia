-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.normalize_to_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:52:32.176171+00:00
-- url     : https://prove2.me/submissions/1768bba0-c1bf-42f0-8587-e287eca6ecc5

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ CubeSphere (fun i => x i / c) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|)
    ⟨j, Finset.mem_univ j⟩
  have hc : 0 < |x i| := (abs_pos.mpr hj).trans_le (hmax j (Finset.mem_univ j))
  refine ⟨|x i|, hc, ?_, i, ?_⟩
  · intro k
    have hle : |x k / (|x i|)| ≤ 1 := by
      rw [abs_div, abs_abs, div_le_one hc]
      exact hmax k (Finset.mem_univ k)
    exact abs_le.mp hle
  · have habs : |x i / (|x i|)| = 1 := by
      rw [abs_div, abs_abs, div_self (ne_of_gt hc)]
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
    · exact Or.inr h
    · exact Or.inl h
end Kourovka.MetabelianEnumeration.ConeVerifier
