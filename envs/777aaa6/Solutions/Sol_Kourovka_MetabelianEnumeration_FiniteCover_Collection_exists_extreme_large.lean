-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.exists_extreme_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:49.280388+00:00
-- url     : https://prove2.me/submissions/6b55dc26-9458-4c60-82e4-2fb5cff22a43

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_le_sum
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
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (reverse : Bool)
    (v : Lattice k) (ρ : ℝ) (hv : ρ ≤ ‖euclidean v‖) :
    ∃ j : Fin k, ρ / k ≤ |(v j : ℝ)| ∧
      ∀ i, precedes reverse i j → |(v i : ℝ)| < ρ / k := by
  classical
  have hk0 : k ≠ 0 := by omega
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  let S : Finset (Fin k) := Finset.univ.filter fun i => ρ / k ≤ |(v i : ℝ)|
  have hS : S.Nonempty := by
    by_contra h
    have hs : ∀ i : Fin k, |(v i : ℝ)| < ρ / k := by
      intro i
      have hi : i ∉ S := fun hi => h ⟨i, hi⟩
      simpa [S] using hi
    have ht : (∑ _i : Fin k, ρ / k) = ρ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hh : (∑ i : Fin k, |(v i : ℝ)|) < ∑ _i : Fin k, ρ / k :=
      Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ (fun i _ => hs i)
    rw [ht] at hh
    exact (not_lt_of_ge hv) ((euclidean_norm_le_sum v).trans_lt hh)
  cases reverse
  · refine ⟨S.min' hS, (Finset.mem_filter.mp (Finset.min'_mem S hS)).2, ?_⟩
    intro i hi
    change i < S.min' hS at hi
    by_contra! hn
    have hm : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hn⟩
    exact (not_le_of_gt hi) (Finset.min'_le S i hm)
  · refine ⟨S.max' hS, (Finset.mem_filter.mp (Finset.max'_mem S hS)).2, ?_⟩
    intro i hi
    change S.max' hS < i at hi
    by_contra! hn
    have hm : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hn⟩
    exact (not_le_of_gt hi) (Finset.le_max' S i hm)
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
