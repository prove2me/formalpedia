-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_PMFToDistribution
-- name    : AnalyticCombinatorics_Ch9_LimitLaws_PMFToDistribution
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T15:15:20.173431+00:00
-- url     : https://prove2.me/theorems/70d77aea-c907-485d-b23b-dc9d1736cea5
-- title:
--   Uniform permutation measures and discrete laws
-- statement:
--   Permutation types receive a measurable structure and the uniform probability measure obtained from the uniform finite PMF. Its pushforward is the actual fixed-point law on Nat; a Poisson measure is packaged as a probability measure. Fixed-point finsets and explicit equivalences with derangements give the exact singleton-count bridge.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/PMFToDistribution.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_FixedPointsPoisson
import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Pointwise pmf convergence on `ℕ` implies weak convergence

This file supplies a reusable discrete bridge from pointwise convergence of
singleton masses on `ℕ` to Mathlib's weak convergence topology on
`ProbabilityMeasure ℕ`, and applies it to the fixed-point count in a uniform
random permutation.
-/

noncomputable section

open Filter
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace PMFToDistribution

open MeasureTheory

namespace FixedPointsPoissonNS

open AnalyticCombinatorics.Ch9.LimitLaws.FixedPointsPoissonNS

instance instMeasurableSpacePermFin (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) :=
  ⊤

/-- Uniform probability measure on permutations of `Fin n`. -/
def uniformPermMeasure (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure

instance uniformPermMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (uniformPermMeasure n) := by
  unfold uniformPermMeasure
  infer_instance

lemma fixedPointCount_aemeasurable (n : ℕ) :
    AEMeasurable (FixedPointsPoissonNS.fixedPointCount n) (uniformPermMeasure n) :=
  (measurable_of_finite _).aemeasurable

/-- The law of the fixed-point count under the uniform permutation measure. -/
def fixedPointLaw (n : ℕ) : ProbabilityMeasure ℕ :=
  ⟨Measure.map (FixedPointsPoissonNS.fixedPointCount n) (uniformPermMeasure n),
    Measure.isProbabilityMeasure_map (fixedPointCount_aemeasurable n)⟩

/-- The Poisson law as a `ProbabilityMeasure`. -/
def poissonProbabilityMeasure (r : ℝ≥0) : ProbabilityMeasure ℕ :=
  ⟨ProbabilityTheory.poissonMeasure r, ProbabilityTheory.isProbabilityMeasurePoisson r⟩

/-- The fixed-point set as a finset. -/
def fixedPointFinset (n : ℕ) (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => σ i = i)

@[simp]
lemma mem_fixedPointFinset {n : ℕ} {σ : Equiv.Perm (Fin n)} {i : Fin n} :
    i ∈ fixedPointFinset n σ ↔ σ i = i := by
  simp [fixedPointFinset]

lemma card_fixedPointFinset (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (fixedPointFinset n σ).card =
      FixedPointsPoissonNS.fixedPointCount n σ := by
  classical
  unfold fixedPointFinset FixedPointsPoissonNS.fixedPointCount
  exact (Fintype.card_ofFinset (Finset.univ.filter (fun i => σ i = i))
    (fun i => by
      change i ∈ Finset.univ.filter (fun i : Fin n => σ i = i) ↔ σ i = i
      simp)).symm

lemma fixedPointFinset_eq_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    fixedPointFinset n σ = s ↔
      ∀ i : Fin n, i ∈ s ↔ σ i = i := by
  constructor
  · intro h i
    rw [← h]
    exact mem_fixedPointFinset
  · intro h
    ext i
    simp [h i]

lemma derangements_subtype_fixedPointFinset_iff {n : ℕ} (s : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    (∀ i : Fin n, ¬ i ∉ (s : Set (Fin n)) ↔ i ∈ Function.fixedPoints σ) ↔
      fixedPointFinset n σ = s := by
  constructor
  · intro h
    refine (fixedPointFinset_eq_iff σ s).2 ?_
    intro i
    have hi := h i
    simpa [Function.mem_fixedPoints_iff] using hi
  · intro h i
    have hi := (fixedPointFinset_eq_iff σ s).1 h i
    simpa [Function.mem_fixedPoints_iff] using hi

/-- Permutations with fixed-point set `s` are derangements on the complement of `s`. -/
def permsWithFixedPointFinsetEquivDerangements {n : ℕ} (s : Finset (Fin n)) :
    {σ : Equiv.Perm (Fin n) // fixedPointFinset n σ = s} ≃
      derangements ({i : Fin n // i ∉ (s : Set (Fin n))}) :=
  ((derangements.subtypeEquiv (fun i : Fin n => i ∉ (s : Set (Fin n)))).trans
    (Equiv.subtypeEquivRight
      (fun σ => derangements_subtype_fixedPointFinset_iff (n := n) s σ))).symm

def permsByFixedPointFinsetEquiv (n j : ℕ) :
    {σ : Equiv.Perm (Fin n) //
      FixedPointsPoissonNS.fixedPointCount n σ = j} ≃
      Σ s : Set.powersetCard (Fin n) j,
        {σ : Equiv.Perm (Fin n) // fixedPointFinset n σ = (s : Finset (Fin n))} where
  toFun σ :=
    ⟨⟨fixedPointFinset n σ.1, by
        rw [Set.powersetCard.mem_iff]
        rw [card_fixedPointFinset n σ.1, σ.2]⟩,
      ⟨σ.1, rfl⟩⟩
  invFun x :=
    ⟨x.2.1, by
      rw [← card_fixedPointFinset n x.2.1, x.2.2]
      exact Set.powersetCard.card_eq x.1⟩
  left_inv σ := by
    ext
    rfl
  right_inv x := by
    cases x with
    | mk s σ =>
      cases σ with
      | mk σ hσ =>
        ext <;> simp [hσ]

end FixedPointsPoissonNS

end PMFToDistribution
end LimitLaws
end Ch9
end AnalyticCombinatorics


