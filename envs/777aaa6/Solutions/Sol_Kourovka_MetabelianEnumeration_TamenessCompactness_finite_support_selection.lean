-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.TamenessCompactness.finite_support_selection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:33.219195+00:00
-- url     : https://prove2.me/submissions/34f670d9-3c5d-4217-a699-5bc0a878b8d6

import Definitions.Def_Kourovka_Covers_FiniteCover
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_coneCover_iff_cubeMargin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_continuous_supportScore
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_cubeSphere_ne_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_isCompact_cubeSphere
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_supportScore_gt_iff


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.TamenessCompactness
open ConeVerifier FiniteCover
namespace Kourovka.MetabelianEnumeration.TamenessCompactness
theorem _root_.solution {k : ℕ} {ι : Type*}
    (support : ι → List (Vec k)) (admissible : ι → Prop)
    (h : ∀ x : Fin k → ℝ, x ≠ 0 →
      ∃ i, admissible i ∧ ∀ u ∈ support i, 0 < dot u x) :
    ∃ selected : List ι, (∀ i ∈ selected, admissible i) ∧
      ConeCover (selected.map support) := by
  classical
  let U (i : {i // admissible i}) : Set (Fin k → ℝ) :=
    {x | 0 < supportScore (support i.1) x}
  have ho : ∀ i, IsOpen (U i) := fun i =>
    isOpen_lt continuous_const (continuous_supportScore (support i.1))
  have hcover : {x : Fin k → ℝ | CubeSphere x} ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨i, hi, hpos⟩ := h x (cubeSphere_ne_zero hx)
    apply Set.mem_iUnion.mpr
    refine ⟨⟨i, hi⟩, ?_⟩
    exact (supportScore_gt_iff (support i) x 0 (by norm_num)).mpr hpos
  obtain ⟨selected, hs⟩ := (isCompact_cubeSphere k).elim_finite_subcover U ho hcover
  refine ⟨selected.toList.map Subtype.val, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact j.2
  · apply (coneCover_iff_cubeMargin _).mpr
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨his, hix⟩ := Set.mem_iUnion.mp hi
    refine ⟨support i.1, List.mem_map.mpr ⟨i.1,
      List.mem_map.mpr ⟨i, Finset.mem_toList.mpr his, rfl⟩, rfl⟩, ?_⟩
    simpa only [Rat.cast_zero] using
      (supportScore_gt_iff (support i.1) x 0 (by norm_num)).mp hix
end Kourovka.MetabelianEnumeration.TamenessCompactness
