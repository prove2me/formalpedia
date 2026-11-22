-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.cube_margin_direction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:07:30.244512+00:00
-- url     : https://prove2.me/submissions/2f21367a-d323-4f57-9ae3-e26c87c9b559

import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverMargin
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_inner_lattice
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_dot_div
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_normalize_to_cube
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_abs
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_le_sum
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_not_precedes_self
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_unitSign
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_add
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_neg
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_norm_abs
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.not_precedes_self
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last



set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection ConeVerifier TamenessCompactness
namespace Kourovka.MetabelianEnumeration.FiniteCover
theorem _root_.solution {k a : ℕ} (data : Datum k a) (hk : 1 ≤ k)
    (ε : ℚ) (hε : 0 < ε)
    (hm : CubeMargin (data.polynomials.map polynomialSupport) ε) :
    ∀ v : Lattice k, v ≠ 0 → ∃ p ∈ data.polynomials,
      ∀ term ∈ p.2, inner ℝ (euclidean v) (euclidean term.1) ≤
        -((ε / k : ℚ) : ℝ) * ‖euclidean v‖ := by
  intro v hv
  let x : Fin k → ℝ := fun i => -(v i : ℝ)
  have hx : x ≠ 0 := by
    intro h
    apply hv
    ext i
    have hi := congrFun h i
    dsimp [x] at hi
    exact_mod_cast (show (v i : ℝ) = 0 by simpa using hi)
  obtain ⟨c, hc, hcube⟩ := normalize_to_cube x hx
  obtain ⟨support, hs, hpos⟩ := hm (fun i => x i / c) hcube
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  refine ⟨p, hp, ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hε0 : (0 : ℝ) < ε := by exact_mod_cast hε
  have hcoord : ∀ i, |(v i : ℝ)| ≤ c := by
    intro i
    have hi := hcube.1 i
    have h := abs_le.mpr hi
    rw [abs_div, abs_of_pos hc] at h
    have h' := (div_le_one hc).mp h
    simpa [x] using h'
  have hnorm : ‖euclidean v‖ ≤ (k : ℝ) * c := by
    apply (euclidean_norm_le_sum v).trans
    calc
      (∑ i, |(v i : ℝ)|) ≤ ∑ _i : Fin k, c := Finset.sum_le_sum (fun i _ => hcoord i)
      _ = _ := by simp
  intro term ht
  have hterm := hpos (fun i => (term.1 i : ℚ)) (List.mem_map.mpr ⟨term, ht, rfl⟩)
  rw [dot_div] at hterm
  have he : dot (fun i => (term.1 i : ℚ)) x =
      -inner ℝ (euclidean v) (euclidean term.1) := by
    simp [dot, x, inner_lattice, Finset.sum_neg_distrib]
  rw [he] at hterm
  have hdot := (lt_div_iff₀ hc).mp hterm
  have hm : (ε : ℝ) / k * ‖euclidean v‖ ≤ (ε : ℝ) * c := by
    calc
      _ ≤ (ε : ℝ) / k * ((k : ℝ) * c) :=
        mul_le_mul_of_nonneg_left hnorm (div_nonneg hε0.le hk0.le)
      _ = _ := by field_simp
  push_cast
  nlinarith
end Kourovka.MetabelianEnumeration.FiniteCover
