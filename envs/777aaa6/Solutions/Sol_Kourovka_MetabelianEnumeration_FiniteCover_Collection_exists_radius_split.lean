-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.exists_radius_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:08:28.855759+00:00
-- url     : https://prove2.me/submissions/505452d3-8a18-41b9-a332-bec50b790a7d

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_le_sum
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_abs
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_exists_extreme_large
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_tailStep_norm_lt
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_prefixStep_sum_lt
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last


attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_add
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_norm_abs

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (reverse : Bool)
    (u v : Lattice k) (ρ : ℝ) (hρ : 2 * (k : ℝ) < ρ)
    (hu : ‖euclidean u‖ ≤ ρ / (2 * k))
    (hv : ρ ≤ ‖euclidean v‖) (hv' : ‖euclidean v‖ < ρ + 1 / (2 * k)) :
    ∃ j : Fin k,
      ‖euclidean (latticeAbs u + latticeAbs (prefixStep reverse v j))‖ < ρ ∧
      ‖euclidean (tailStep reverse v j)‖ < ρ := by
  obtain ⟨j, hj, hsmall⟩ := exists_extreme_large hk reverse v ρ hv
  refine ⟨j, ?_, tailStep_norm_lt hk reverse v j ρ hρ hj hv'⟩
  have hp := prefixStep_sum_lt hk reverse v j ρ hρ hsmall
  have hnorm : ‖euclidean (latticeAbs u + latticeAbs (prefixStep reverse v j))‖ ≤
      ‖euclidean u‖ + ‖euclidean (prefixStep reverse v j)‖ := by
    rw [euclidean_add, ← euclidean_norm_abs u, ← euclidean_norm_abs (prefixStep reverse v j)]
    exact norm_add_le _ _
  have hp' := euclidean_norm_le_sum (prefixStep reverse v j)
  linarith
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
