-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.tailStep_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:07:19.337011+00:00
-- url     : https://prove2.me/submissions/843b08d1-aade-49f6-8b60-103dac16d213

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_abs
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_not_precedes_self
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_tailStep_norm_sq_le
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
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_norm_abs
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_unitSign
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.not_precedes_self

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (reverse : Bool) (v : Lattice k)
    (j : Fin k) (ρ : ℝ) (hρ : 2 * (k : ℝ) < ρ)
    (hlarge : ρ / k ≤ |(v j : ℝ)|)
    (hv : ‖euclidean v‖ < ρ + 1 / (2 * k)) :
    ‖euclidean (tailStep reverse v j)‖ < ρ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hρ0 : 0 < ρ := by linarith
  let α : ℝ := 1 / (2 * k)
  have hα0 : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 / 2 := by
    dsimp [α]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
    linarith
  have hrk : 2 < ρ / k := (lt_div_iff₀ hk0).mpr (by nlinarith)
  have he : (ρ + α) ^ 2 - 2 * (ρ / k) + 1 = ρ ^ 2 - ρ / k + 1 + α ^ 2 := by
    dsimp [α]
    field_simp
    ring
  have hcalc : (ρ + α) ^ 2 - 2 * (ρ / k) + 1 < ρ ^ 2 := by
    rw [he]
    nlinarith
  have hv2 : ‖euclidean v‖ ^ 2 < (ρ + α) ^ 2 := by
    change ‖euclidean v‖ < ρ + α at hv
    nlinarith [norm_nonneg (euclidean v)]
  have ht := tailStep_norm_sq_le reverse v j
  have ht2 : ‖euclidean (tailStep reverse v j)‖ ^ 2 < ρ ^ 2 := by nlinarith
  nlinarith [norm_nonneg (euclidean (tailStep reverse v j))]
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
