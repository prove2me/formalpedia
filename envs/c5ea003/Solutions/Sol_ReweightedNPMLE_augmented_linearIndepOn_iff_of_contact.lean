-- Prove2me | solution 1 for ReweightedNPMLE.augmented_linearIndepOn_iff_of_contact
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:52:48.276367+00:00
-- url     : https://prove2.me/submissions/13c4952f-04d5-465e-876e-8857c3022f28

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber

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
/-- On a contact hyperplane, affine independence and linear independence
coincide.  This is the finite-dimensional version of the likelihood contact
identity used for optimizer supports in the paper. -/
theorem solution
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (S : Finset (Fin m)) (b : E →ₗ[ℝ] ℝ)
    (hcontact : ∀ i ∈ S, b (A i) = 1) :
    LinearIndepOn ℝ (augmentedDictionary A) (S : Set (Fin m)) ↔
      LinearIndepOn ℝ A (S : Set (Fin m)) := by
  classical
  rw [linearIndepOn_finset_iff, linearIndepOn_finset_iff]
  constructor
  · intro haug f hf
    have hsum : ∑ i ∈ S, f i = 0 := by
      calc
        (∑ i ∈ S, f i) = ∑ i ∈ S, f i * 1 := by simp
        _ = ∑ i ∈ S, f i * b (A i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcontact i hi]
        _ = b (∑ i ∈ S, f i • A i) := by
          rw [map_sum]
          simp
        _ = 0 := by rw [hf, map_zero]
    apply haug f
    apply Prod.ext
    · rw [Prod.fst_sum]
      simpa [augmentedDictionary] using hsum
    · rw [Prod.snd_sum]
      simpa [augmentedDictionary] using hf
  · intro hA f hf
    apply hA f
    have hsnd := congrArg (AddMonoidHom.snd ℝ E) hf
    simpa [augmentedDictionary] using hsnd
