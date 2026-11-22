-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.prefixStep_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:44.13861+00:00
-- url     : https://prove2.me/submissions/726afd57-1c2c-45be-8f04-bfd573de34c7

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_abs
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_not_precedes_self
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
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (reverse : Bool) (v : Lattice k) (j : Fin k)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hsmall : ∀ i, precedes reverse i j → |(v i : ℝ)| < ρ / k) :
    (∑ i, |(prefixStep reverse v j i : ℝ)|) ≤ ((k : ℝ) - 1) * (ρ / k) + 1 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hp : 0 ≤ ρ / k := div_nonneg hρ hk'.le
  calc
    (∑ i, |(prefixStep reverse v j i : ℝ)|) ≤ ∑ i : Fin k, if i = j then (1 : ℝ) else ρ / k := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hij : i = j
      · subst i
        simp [prefixStep, ← Int.cast_abs]
      · by_cases hi : precedes reverse i j
        · simpa [prefixStep, hi, hij] using (hsmall i hi).le
        · simpa [prefixStep, hi, hij] using hp
    _ = ((k : ℝ) - 1) * (ρ / k) + 1 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      have he : (∑ i ∈ Finset.univ.erase j, if i = j then (1 : ℝ) else ρ / k) =
          (k - 1 : ℕ) * (ρ / k) := by
        calc
          _ = ∑ _i ∈ (Finset.univ : Finset (Fin k)).erase j, ρ / k := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [(Finset.mem_erase.mp hi).1]
          _ = _ := by simp
      rw [he]
      simp [Nat.cast_sub hk]
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
