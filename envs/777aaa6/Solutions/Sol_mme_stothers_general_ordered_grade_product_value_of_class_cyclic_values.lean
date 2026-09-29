-- Prove2me | solution 1 for mme_stothers_general_ordered_grade_product_value_of_class_cyclic_values
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-09T04:46:50.316101+00:00
-- url     : https://prove2.me/submissions/af0c8ad3-a7e0-481c-81e7-bcd32bdc1c5d

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_stothers_oriented_cyclic_classes
import Theorems.Thm_mme_HasTauValueAtLeast_kronFin_multiplicities_of_each_strict_below_product
import Theorems.Thm_mme_HasTauValueAtLeast_permObj_swapFirstTwo
import Theorems.Thm_mme_stothers_cwFourth_cyclic_swapped_block_iso
import Theorems.Thm_mme_stothers_general_ordered_grade_product_iso_oriented_cyclic_classes
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

private theorem oriented_endpoint_product
    (f : Fin 10 → ℝ) (c : Fin 10 → ℕ) :
    (∏ t : Fin 15,
      f (MME.StothersFourth.fixedOrientedClass t) ^
        c (MME.StothersFourth.fixedOrientedClass t)) =
    ∏ r : Fin 10,
      f r ^ (MME.StothersFourth.classMultiplicity r * c r) := by
  classical
  have hcard : ∀ r : Fin 10,
      Fintype.card {t : Fin 15 //
        MME.StothersFourth.fixedOrientedClass t = r} =
        MME.StothersFourth.classMultiplicity r := by
    intro r
    fin_cases r <;> decide
  let fiberEquiv : ∀ r : Fin 10,
      Fin (MME.StothersFourth.classMultiplicity r) ≃
        {t : Fin 15 // MME.StothersFourth.fixedOrientedClass t = r} :=
    fun r ↦ Fintype.equivOfCardEq (by
      simp only [Fintype.card_fin]
      exact (hcard r).symm)
  let e : (Σ r : Fin 10,
      Fin (MME.StothersFourth.classMultiplicity r)) ≃ Fin 15 :=
    (Equiv.sigmaCongrRight fiberEquiv).trans
      (Equiv.sigmaFiberEquiv MME.StothersFourth.fixedOrientedClass)
  calc
    (∏ t : Fin 15,
        f (MME.StothersFourth.fixedOrientedClass t) ^
          c (MME.StothersFourth.fixedOrientedClass t)) =
        ∏ z : Σ r : Fin 10,
            Fin (MME.StothersFourth.classMultiplicity r),
          f (MME.StothersFourth.fixedOrientedClass (e z)) ^
            c (MME.StothersFourth.fixedOrientedClass (e z)) := by
      symm
      exact Equiv.prod_comp e (fun t : Fin 15 ↦
        f (MME.StothersFourth.fixedOrientedClass t) ^
          c (MME.StothersFourth.fixedOrientedClass t))
    _ = ∏ r : Fin 10,
        ∏ _j : Fin (MME.StothersFourth.classMultiplicity r),
          f r ^ c r := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro r _
      apply Finset.prod_congr rfl
      intro j _
      have he : MME.StothersFourth.fixedOrientedClass (e ⟨r, j⟩) = r := by
        change MME.StothersFourth.fixedOrientedClass
          ((fiberEquiv r j).1) = r
        exact (fiberEquiv r j).2
      rw [he]
    _ = ∏ r : Fin 10,
        f r ^ (MME.StothersFourth.classMultiplicity r * c r) := by
      apply Finset.prod_congr rfl
      intro r _
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← pow_mul]
      rw [Nat.mul_comm]

private theorem classRep_block_eq_constituent
    {K : Type u} [Field K] (r : Fin 10) :
    (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
        (MME.StothersFourth.classRep r) =
      MME.StothersFourth.cwFourthConstituent K 6
        (MME.StothersFourth.classRep r 0)
        (MME.StothersFourth.classRep r 1)
        (MME.StothersFourth.classRep r 2) := by
  fin_cases r <;> rfl

theorem solution
    {K : Type u} [Field K]
    (base : Fin 10 → ℕ) (tau : ℝ)
    (hclass : ∀ (r : Fin 10) (V : ℝ),
      0 ≤ V → V < MME.StothersFourth.classValue 6 tau r →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6
            (MME.StothersFourth.classRep r 0)
            (MME.StothersFourth.classRep r 1)
            (MME.StothersFourth.classRep r 2))) tau V) :
    ∀ (m : ℕ) (W : ℝ),
      0 ≤ W →
      W < (∏ r : Fin 10,
        (MME.StothersFourth.classValue 6 tau r) ^
          (MME.StothersFourth.classMultiplicity r *
            MME.StothersFourth.genProfileCount base m r)) →
      let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
        classical
        simpa only [Fintype.card_fun, Fintype.card_fin, pow_succ,
          pow_zero, mul_one] using
          (Fintype.equivFin (Fin 3 → Fin 9))
      HasTauValueAtLeast
        (TensorObj.kronFin 729 (fun s ↦
          ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
            (e.symm s)).kronPow
              (MME.StothersFourth.genJointMultiplicity base m (e.symm s))))
        tau W := by
  intro m W hW hstrict
  let T : Fin 15 → TensorObj K 3 := fun t ↦
    cyclicSymmetrization
      ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
        (MME.StothersFourth.fixedOrientedRep t))
  let multiplicity : Fin 15 → ℕ := fun t ↦
    MME.StothersFourth.genProfileCount base m
      (MME.StothersFourth.fixedOrientedClass t)
  let endpoint : Fin 15 → ℝ := fun t ↦
    MME.StothersFourth.classValue 6 tau
      (MME.StothersFourth.fixedOrientedClass t)
  have hendpoint : ∀ t, 0 < endpoint t := by
    intro t
    dsimp only [endpoint]
    generalize MME.StothersFourth.fixedOrientedClass t = r
    fin_cases r <;>
      norm_num [MME.StothersFourth.classValue,
        MME.StothersFourth.E, MME.StothersFourth.H,
        MME.StothersFourth.L] <;> positivity
  have hlocal : ∀ (t : Fin 15) (V : ℝ),
      0 ≤ V → V < endpoint t →
      HasTauValueAtLeast (T t) tau V := by
    intro t V hV hVstrict
    have hrepresentative (r : Fin 10)
        (hVstrictR : V < MME.StothersFourth.classValue 6 tau r) :
        HasTauValueAtLeast
          (cyclicSymmetrization
            ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
              (MME.StothersFourth.classRep r))) tau V := by
      rw [classRep_block_eq_constituent r]
      exact hclass r V hV hVstrictR
    fin_cases t
    · simpa only [T, MME.StothersFourth.fixedOrientedRep,
        Matrix.cons_val_zero] using hrepresentative (0 : Fin 10) (by
          simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
            hVstrict)
    · simpa [T, MME.StothersFourth.fixedOrientedRep] using
        hrepresentative (1 : Fin 10) (by
          simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
            hVstrict)
    · have hs := mme_HasTauValueAtLeast_permObj_swapFirstTwo
          (hrepresentative (1 : Fin 10) (by
            simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
              hVstrict))
      exact mme_HasTauValueAtLeast_mono_restrict
        (mme_stothers_cwFourth_cyclic_swapped_block_iso
          (K := K) 6 (MME.StothersFourth.classRep 1)).2 hs
    · simpa [T, MME.StothersFourth.fixedOrientedRep] using
        hrepresentative (2 : Fin 10) (by
          simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
            hVstrict)
    · have hs := mme_HasTauValueAtLeast_permObj_swapFirstTwo
          (hrepresentative (2 : Fin 10) (by
            simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
              hVstrict))
      exact mme_HasTauValueAtLeast_mono_restrict
        (mme_stothers_cwFourth_cyclic_swapped_block_iso
          (K := K) 6 (MME.StothersFourth.classRep 2)).2 hs
    · simpa [T, MME.StothersFourth.fixedOrientedRep] using
        hrepresentative (3 : Fin 10) (by
          simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
            hVstrict)
    · have hs := mme_HasTauValueAtLeast_permObj_swapFirstTwo
          (hrepresentative (3 : Fin 10) (by
            simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
              hVstrict))
      exact mme_HasTauValueAtLeast_mono_restrict
        (mme_stothers_cwFourth_cyclic_swapped_block_iso
          (K := K) 6 (MME.StothersFourth.classRep 3)).2 hs
    · simpa [T, MME.StothersFourth.fixedOrientedRep] using
        hrepresentative (4 : Fin 10) (by
          simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
            hVstrict)
    · simpa [T, MME.StothersFourth.fixedOrientedRep] using
        hrepresentative (5 : Fin 10) (by
          simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
            hVstrict)
    · simpa [T, MME.StothersFourth.fixedOrientedRep] using
        hrepresentative (6 : Fin 10) (by
          simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
            hVstrict)
    · have hs := mme_HasTauValueAtLeast_permObj_swapFirstTwo
          (hrepresentative (6 : Fin 10) (by
            simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
              hVstrict))
      exact mme_HasTauValueAtLeast_mono_restrict
        (mme_stothers_cwFourth_cyclic_swapped_block_iso
          (K := K) 6 (MME.StothersFourth.classRep 6)).2 hs
    · simpa [T, MME.StothersFourth.fixedOrientedRep] using
        hrepresentative (7 : Fin 10) (by
          simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
            hVstrict)
    · have hs := mme_HasTauValueAtLeast_permObj_swapFirstTwo
          (hrepresentative (7 : Fin 10) (by
            simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
              hVstrict))
      exact mme_HasTauValueAtLeast_mono_restrict
        (mme_stothers_cwFourth_cyclic_swapped_block_iso
          (K := K) 6 (MME.StothersFourth.classRep 7)).2 hs
    · simpa [T, MME.StothersFourth.fixedOrientedRep] using
        hrepresentative (8 : Fin 10) (by
          simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
            hVstrict)
    · simpa [T, MME.StothersFourth.fixedOrientedRep] using
        hrepresentative (9 : Fin 10) (by
          simpa [endpoint, MME.StothersFourth.fixedOrientedClass] using
            hVstrict)
  have hendpointProduct :
      (∏ t : Fin 15, endpoint t ^ multiplicity t) =
        ∏ r : Fin 10,
          (MME.StothersFourth.classValue 6 tau r) ^
            (MME.StothersFourth.classMultiplicity r *
              MME.StothersFourth.genProfileCount base m r) := by
    simpa only [endpoint, multiplicity] using
      oriented_endpoint_product
        (MME.StothersFourth.classValue 6 tau)
        (MME.StothersFourth.genProfileCount base m)
  have hproduct : HasTauValueAtLeast
      (TensorObj.kronFin 15
        (fun t ↦ (T t).kronPow (multiplicity t))) tau W := by
    exact
      mme_HasTauValueAtLeast_kronFin_multiplicities_of_each_strict_below_product
        T multiplicity tau endpoint hendpoint hlocal W hW (by
          rw [hendpointProduct]
          exact hstrict)
  have hregroup : TensorObj.Restrict
      (TensorObj.kronFin 15
        (fun t ↦ (T t).kronPow (multiplicity t)))
      (let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
          classical
          simpa only [Fintype.card_fun, Fintype.card_fin, pow_succ,
            pow_zero, mul_one] using
            (Fintype.equivFin (Fin 3 → Fin 9))
        TensorObj.kronFin 729 (fun s ↦
          ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
            (e.symm s)).kronPow
              (MME.StothersFourth.genJointMultiplicity base m (e.symm s)))) := by
    simpa only [T, multiplicity] using
      (mme_stothers_general_ordered_grade_product_iso_oriented_cyclic_classes
        (K := K) base m).1
  exact mme_HasTauValueAtLeast_mono_restrict hregroup hproduct

