-- Prove2me | solution 1 for ReweightedNPMLE.contact_eq_one_on_coefficientSupport
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:53:31.616807+00:00
-- url     : https://prove2.me/submissions/a39a6aac-a10a-401d-964f-7cb8750a1641

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























@[simp] theorem mem_coefficientSupport {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    i ∈ coefficientSupport p ↔ p i ≠ 0 := by
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
/-- A supporting functional which is at most one on the dictionary equals one
at every active atom of a probability mixture on its contact hyperplane. -/
theorem solution
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ) (b : E →ₗ[ℝ] ℝ)
    (hp : p ∈ finiteMixtureFiber A v) (hbv : b v = 1)
    (hbA : ∀ i, b (A i) ≤ 1) :
    ∀ i ∈ coefficientSupport p, b (A i) = 1 := by
  classical
  have hterm_nonneg (i : Fin m) : 0 ≤ p i * (1 - b (A i)) :=
    mul_nonneg (hp.1.1 i) (sub_nonneg.mpr (hbA i))
  have hsumzero : ∑ i : Fin m, p i * (1 - b (A i)) = 0 := by
    calc
      (∑ i : Fin m, p i * (1 - b (A i))) =
          ∑ i, (p i - p i * b (A i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, p i) - ∑ i, p i * b (A i) :=
        Finset.sum_sub_distrib (s := Finset.univ)
          (fun i ↦ p i) (fun i ↦ p i * b (A i))
      _ = 1 - b (finiteMixtureValue A p) := by
        rw [hp.1.2, finiteMixtureValue, map_sum]
        simp only [map_smul, smul_eq_mul]
      _ = 0 := by rw [hp.2, hbv, sub_self]
  intro i hi
  have hzero : p i * (1 - b (A i)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hterm_nonneg j).mp hsumzero i
      (Finset.mem_univ i)
  have hpne : p i ≠ 0 := (mem_coefficientSupport p i).mp hi
  rcases mul_eq_zero.mp hzero with hpi | hcontact
  · exact (hpne hpi).elim
  · linarith
