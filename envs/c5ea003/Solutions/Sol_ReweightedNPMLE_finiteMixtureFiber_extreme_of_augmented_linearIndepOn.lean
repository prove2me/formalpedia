-- Prove2me | solution 1 for ReweightedNPMLE.finiteMixtureFiber_extreme_of_augmented_linearIndepOn
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:53:19.118854+00:00
-- url     : https://prove2.me/submissions/24103a24-2c33-43c9-9d80-716e5dbe508d

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber

-- Inline helpers preserved from ReweightedNPMLE.FiniteOptimizerFiber.
section
/-!
# Extreme finite mixture fibers

This file isolates the finite-dimensional core of the paper's optimizer-fiber
lemma.  A probability vector represents a finite mixing law.  If the
dictionary vectors indexed by its nonzero masses are linearly independent,
then that representation is an extreme point of the fiber of all probability
vectors with the same fitted value.
-/

open Set
open scoped BigOperators

namespace ReweightedNPMLE

























theorem not_mem_coefficientSupport_iff {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    i ∉ coefficientSupport p ↔ p i = 0 := by
  simp [coefficientSupport]

























end ReweightedNPMLE
end

/-!
# Extreme finite mixture fibers

This file isolates the finite-dimensional core of the paper's optimizer-fiber
lemma.  A probability vector represents a finite mixing law.  If the
dictionary vectors indexed by its nonzero masses are linearly independent,
then that representation is an extreme point of the fiber of all probability
vectors with the same fitted value.
-/

open Set
open scoped BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The exact finite-fiber criterion: a probability vector is extreme when
the augmented dictionary vectors on its support are linearly independent.
The extra coordinate records the total-mass constraint. -/
theorem solution
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ)
    (hp : p ∈ finiteMixtureFiber A v)
    (hlin : LinearIndepOn ℝ (augmentedDictionary A)
      (coefficientSupport p : Set (Fin m))) :
    p ∈ (finiteMixtureFiber A v).extremePoints ℝ := by
  classical
  rw [mem_extremePoints_iff_left]
  refine ⟨hp, ?_⟩
  intro q hq r hr hpqr
  rw [openSegment_eq_image] at hpqr
  rcases hpqr with ⟨t, ht, hrepr⟩
  rcases ht with ⟨htzero, htone⟩
  let S := coefficientSupport p
  have hqnonneg (i : Fin m) : 0 ≤ q i := hq.1.1 i
  have hrnonneg (i : Fin m) : 0 ≤ r i := hr.1.1 i
  have hqzero (i : Fin m) (hi : i ∉ S) : q i = 0 := by
    have hpzero : p i = 0 :=
      (not_mem_coefficientSupport_iff p i).mp hi
    have hcoord := congrFun hrepr i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcoord
    rw [hpzero] at hcoord
    have hleft : 0 ≤ (1 - t) * q i :=
      mul_nonneg (sub_nonneg.mpr htone.le) (hqnonneg i)
    have hright : 0 ≤ t * r i := mul_nonneg htzero.le (hrnonneg i)
    have hleftzero : (1 - t) * q i = 0 := by linarith
    rcases mul_eq_zero.mp hleftzero with ht | hq
    · linarith
    · exact hq
  have hpzero (i : Fin m) (hi : i ∉ S) : p i = 0 :=
    (not_mem_coefficientSupport_iff p i).mp hi
  have hall : ∑ i : Fin m, (q i - p i) • augmentedDictionary A i = 0 := by
    apply Prod.ext
    · rw [Prod.fst_sum]
      simp [augmentedDictionary, Finset.sum_sub_distrib, hq.1.2, hp.1.2]
    · rw [Prod.snd_sum]
      simp only [augmentedDictionary]
      calc
        (∑ i : Fin m, (q i - p i) • A i) =
            finiteMixtureValue A q - finiteMixtureValue A p := by
          simp [finiteMixtureValue, sub_smul, Finset.sum_sub_distrib]
        _ = 0 := by rw [hq.2, hp.2, sub_self]
  have hsupport : ∑ i ∈ S, (q i - p i) • augmentedDictionary A i = 0 := by
    calc
      (∑ i ∈ S, (q i - p i) • augmentedDictionary A i) =
          ∑ i : Fin m, (q i - p i) • augmentedDictionary A i := by
        rw [← Finset.sum_subset (Finset.subset_univ S)]
        intro i _ hi
        rw [hqzero i hi, hpzero i hi, sub_self, zero_smul]
      _ = 0 := hall
  have hcoeff : ∀ i ∈ S, q i - p i = 0 :=
    (linearIndepOn_finset_iff.mp hlin) (fun i ↦ q i - p i) hsupport
  funext i
  by_cases hi : i ∈ S
  · exact sub_eq_zero.mp (hcoeff i hi)
  · rw [hqzero i hi, hpzero i hi]
