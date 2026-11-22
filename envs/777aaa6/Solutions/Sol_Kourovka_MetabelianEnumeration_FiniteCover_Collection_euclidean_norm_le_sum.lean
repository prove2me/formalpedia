-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_norm_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:52:05.996503+00:00
-- url     : https://prove2.me/submissions/df0b4697-cad3-493e-879b-4cda90f39480

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last


attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_add
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_neg

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (v : Lattice k) :
    ‖euclidean v‖ ≤ ∑ i, |(v i : ℝ)| := by
  have h : euclidean v = ∑ i, EuclideanSpace.single i (v i : ℝ) := by
    ext j
    change (v j : ℝ) = (EuclideanSpace.projₗ j) (∑ i, EuclideanSpace.single i (v i : ℝ))
    rw [map_sum]
    change (v j : ℝ) = ∑ i, (EuclideanSpace.single i (v i : ℝ)) j
    simp [EuclideanSpace.single_apply]
  rw [h]
  exact (norm_sum_le _ _).trans_eq (by simp [EuclideanSpace.norm_single, Real.norm_eq_abs])
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
