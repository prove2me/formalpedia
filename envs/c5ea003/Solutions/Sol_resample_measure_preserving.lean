-- Prove2me | solution 1 for resample_measure_preserving
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T02:30:45.551212+00:00
-- url     : https://prove2.me/submissions/ac51503b-b70a-40be-8695-b799dbe0dff2

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (fun p : (∀ j, α j) × (∀ j, α j) => Function.update p.1 i (p.2 i))
      ((Measure.pi μ).prod (Measure.pi μ)) (Measure.pi μ) := by
  have hmeas : Measurable
      (fun p : (∀ j, α j) × (∀ j, α j) => Function.update p.1 i (p.2 i)) := by
    fun_prop
  refine ⟨hmeas, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (∀ j, α j) × (∀ j, α j) => Function.update p.1 i (p.2 i)) ⁻¹'
      (Set.univ.pi s)
      = (Set.univ.pi (fun j => if j = i then Set.univ else s j))
        ×ˢ (Function.eval i ⁻¹' s i) := by
    ext ⟨ω, ω'⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod,
      Function.eval]
    constructor
    · intro h
      refine ⟨fun j => ?_, ?_⟩
      · split_ifs with hj
        · trivial
        · have := h j; rwa [Function.update_of_ne hj] at this
      · have := h i; rwa [Function.update_self] at this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; rwa [Function.update_self]
      · rw [Function.update_of_ne hj]; have := h1 j; rwa [if_neg hj] at this
  rw [hpre, Measure.prod_prod]
  have hA : Measure.pi μ (Set.univ.pi (fun j => if j = i then Set.univ else s j))
      = ∏ j, μ j (if j = i then Set.univ else s j) := by
    rw [Measure.pi_pi]
  have hB : Measure.pi μ (Function.eval i ⁻¹' s i) = μ i (s i) := by
    have := (measurePreserving_eval μ i).map_eq
    rw [← this, Measure.map_apply (measurable_pi_apply i) (hs i)]
  rw [hA, hB]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
      ← Finset.prod_erase_mul _ (fun j => μ j (s j)) (Finset.mem_univ i)]
  have herase : (∏ x ∈ Finset.univ.erase i, μ x (if x = i then univ else s x))
      = ∏ x ∈ Finset.univ.erase i, μ x (s x) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj)]
  rw [herase, if_pos rfl, measure_univ, mul_one]
