-- Prove2me | solution 1 for MarkovChainCLT.tvDist_le_sSup_of_isSetRing
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T21:38:30.719468+00:00
-- url     : https://prove2.me/submissions/1a6e6de0-f584-4956-a802-a216fcfa9b1a

import Definitions.Def_TotalVariationDist
import Mathlib.MeasureTheory.Measure.MeasuredSets

open MeasureTheory MeasurableSpace
open MarkovChainCLT
open scoped ENNReal NNReal symmDiff

set_option maxHeartbeats 2000000

/-- The total variation distance is already attained, up to nothing, on a generating ring. -/
theorem solution {X : Type*} [mX : MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (C : Set (Set X)) (hC : IsSetRing C) (hCm : ∀ s ∈ C, MeasurableSet s)
    (hcov : ∃ D : Set (Set X), D.Countable ∧ D ⊆ C ∧ (μ + ν) (⋃₀ D)ᶜ = 0)
    (hgen : mX = generateFrom C) :
    tvDist μ ν ≤ sSup {r | ∃ A ∈ C, r = |(μ A).toReal - (ν A).toReal|} := by
  set S' : Set ℝ := {r | ∃ A ∈ C, r = |(μ A).toReal - (ν A).toReal|} with hS'
  -- `S'` is bounded above and contains `0`
  have hbdd' : BddAbove S' := by
    refine ⟨(μ Set.univ).toReal + (ν Set.univ).toReal, ?_⟩
    rintro r ⟨A, hA, rfl⟩
    have h1 : (μ A).toReal ≤ (μ Set.univ).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
    have h2 : (ν A).toReal ≤ (ν Set.univ).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
    rw [abs_le]
    constructor <;>
      [linarith [ENNReal.toReal_nonneg (a := μ A), ENNReal.toReal_nonneg (a := ν Set.univ)];
       linarith [ENNReal.toReal_nonneg (a := ν A), ENNReal.toReal_nonneg (a := μ Set.univ)]]
  have hzero : (0:ℝ) ∈ S' := ⟨∅, hC.empty_mem, by simp⟩
  have hS0 : 0 ≤ sSup S' := le_csSup hbdd' hzero
  -- bound each element of the defining set of `tvDist`
  refine Real.sSup_le ?_ hS0
  rintro r ⟨A, hA, rfl⟩
  -- approximate `A` by a member of `C`, with error measured by `μ + ν`
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨t, htC, ht⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := μ + ν) hC hcov hgen hA (ε := ENNReal.ofReal (ε/2)) (by simp; linarith)
  have htm : MeasurableSet t := hCm t htC
  -- the two measures of the symmetric difference are small
  have hsymm : MeasurableSet (t ∆ A) := htm.symmDiff hA
  have hμs : (μ (t ∆ A)).toReal ≤ ε/2 := by
    have hle : μ (t ∆ A) ≤ (μ + ν) (t ∆ A) := by
      simp only [Measure.coe_add, Pi.add_apply]
      exact le_add_right le_rfl
    have : μ (t ∆ A) < ENNReal.ofReal (ε/2) := lt_of_le_of_lt hle ht
    exact ENNReal.toReal_le_of_le_ofReal (by linarith) this.le
  have hνs : (ν (t ∆ A)).toReal ≤ ε/2 := by
    have hle : ν (t ∆ A) ≤ (μ + ν) (t ∆ A) := by
      simp only [Measure.coe_add, Pi.add_apply]
      exact le_add_left le_rfl
    have : ν (t ∆ A) < ENNReal.ofReal (ε/2) := lt_of_le_of_lt hle ht
    exact ENNReal.toReal_le_of_le_ofReal (by linarith) this.le
  -- a measure difference is controlled by the symmetric difference
  have hdiff : ∀ (ρ : Measure X), IsFiniteMeasure ρ →
      |(ρ A).toReal - (ρ t).toReal| ≤ (ρ (t ∆ A)).toReal := by
    intro ρ hρ
    haveI := hρ
    have hA1 : ρ A = ρ (A ∩ t) + ρ (A \ t) := (measure_inter_add_diff A htm).symm
    have ht1 : ρ t = ρ (t ∩ A) + ρ (t \ A) := (measure_inter_add_diff t hA).symm
    have hcomm : ρ (A ∩ t) = ρ (t ∩ A) := by rw [Set.inter_comm]
    have hsplit : ρ (t ∆ A) = ρ (t \ A) + ρ (A \ t) := by
      rw [Set.symmDiff_def]
      exact measure_union (Set.disjoint_left.mpr (fun x hx hx' => hx.2 hx'.1)) (hA.diff htm)
    have h1 : (ρ A).toReal = (ρ (A ∩ t)).toReal + (ρ (A \ t)).toReal := by
      rw [hA1, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    have h2 : (ρ t).toReal = (ρ (A ∩ t)).toReal + (ρ (t \ A)).toReal := by
      rw [ht1, hcomm, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    have h3 : (ρ (t ∆ A)).toReal = (ρ (t \ A)).toReal + (ρ (A \ t)).toReal := by
      rw [hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    rw [abs_le]
    constructor <;> [
      linarith [ENNReal.toReal_nonneg (a := ρ (A \ t)), ENNReal.toReal_nonneg (a := ρ (t \ A))];
      linarith [ENNReal.toReal_nonneg (a := ρ (A \ t)), ENNReal.toReal_nonneg (a := ρ (t \ A))]]
  have hμd := hdiff μ inferInstance
  have hνd := hdiff ν inferInstance
  -- conclude
  have hmem : |(μ t).toReal - (ν t).toReal| ∈ S' := ⟨t, htC, rfl⟩
  have hle' : |(μ t).toReal - (ν t).toReal| ≤ sSup S' := le_csSup hbdd' hmem
  have hkey : |(μ A).toReal - (ν A).toReal| - |(μ t).toReal - (ν t).toReal|
      ≤ (μ (t ∆ A)).toReal + (ν (t ∆ A)).toReal := by
    have := abs_sub_abs_le_abs_sub ((μ A).toReal - (ν A).toReal) ((μ t).toReal - (ν t).toReal)
    have hb : |((μ A).toReal - (ν A).toReal) - ((μ t).toReal - (ν t).toReal)|
        ≤ |(μ A).toReal - (μ t).toReal| + |(ν A).toReal - (ν t).toReal| := by
      have : ((μ A).toReal - (ν A).toReal) - ((μ t).toReal - (ν t).toReal)
          = ((μ A).toReal - (μ t).toReal) - ((ν A).toReal - (ν t).toReal) := by ring
      rw [this]
      exact abs_sub _ _
    linarith [hμd, hνd]
  linarith [hkey, hle', hμs, hνs]
