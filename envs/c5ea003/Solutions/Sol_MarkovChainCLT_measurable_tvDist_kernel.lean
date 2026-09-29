-- Prove2me | solution 1 for MarkovChainCLT.measurable_tvDist_kernel
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T21:47:07.124404+00:00
-- url     : https://prove2.me/submissions/fb0816ec-ad16-4ee5-b9e1-990f4a679f3e

import Theorems.Thm_MarkovChainCLT_tvDist_le_sSup_of_isSetRing
import Theorems.Thm_MarkovChainCLT_exists_countable_isSetRing_generateFrom
import Mathlib.Probability.Kernel.Basic

open MeasureTheory MeasurableSpace ProbabilityTheory Set
open MarkovChainCLT
open scoped ENNReal NNReal symmDiff

set_option maxHeartbeats 2000000

theorem solution {X Y : Type*} [MeasurableSpace X]
    [mY : MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
    (Q : Kernel X Y) [IsMarkovKernel Q] (ν : Measure Y) [IsProbabilityMeasure ν] :
    Measurable (fun x => tvDist (Q x) ν) := by
  classical
  obtain ⟨C, hCcount, hCring, hCm, hCuniv, hCgen⟩ :=
    MarkovChainCLT.exists_countable_isSetRing_generateFrom (X := Y)
  have hCne : C.Nonempty := ⟨Set.univ, hCuniv⟩
  obtain ⟨e, he⟩ := hCcount.exists_eq_range hCne
  -- the defining set of `tvDist` is bounded above by `2`
  have hbdd : ∀ (μ : Measure Y), IsProbabilityMeasure μ →
      BddAbove {r | ∃ A : Set Y, MeasurableSet A ∧ r = |(μ A).toReal - (ν A).toReal|} := by
    intro μ hμ
    haveI := hμ
    refine ⟨2, ?_⟩
    rintro r ⟨A, hA, rfl⟩
    have h1 : (μ A).toReal ≤ 1 := by
      refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
      simpa using prob_le_one
    have h2 : (ν A).toReal ≤ 1 := by
      refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
      simpa using prob_le_one
    rw [abs_le]
    constructor <;>
      [linarith [ENNReal.toReal_nonneg (a := μ A)]; linarith [ENNReal.toReal_nonneg (a := ν A)]]
  -- `tvDist (Q x) ν` is a countable supremum
  have hEq : ∀ x, tvDist (Q x) ν = ⨆ n : ℕ, |((Q x) (e n)).toReal - (ν (e n)).toReal| := by
    intro x
    have hcov : ∃ D : Set (Set Y), D.Countable ∧ D ⊆ C ∧ ((Q x) + ν) (⋃₀ D)ᶜ = 0 := by
      refine ⟨{Set.univ}, Set.countable_singleton _, by simpa using hCuniv, ?_⟩
      simp
    have hle := MarkovChainCLT.tvDist_le_sSup_of_isSetRing (Q x) ν C hCring hCm hcov hCgen.symm
    have hset : {r | ∃ A ∈ C, r = |((Q x) A).toReal - (ν A).toReal|}
        = Set.range (fun n : ℕ => |((Q x) (e n)).toReal - (ν (e n)).toReal|) := by
      ext r
      constructor
      · rintro ⟨A, hA, rfl⟩
        rw [he] at hA
        obtain ⟨n, rfl⟩ := hA
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨e n, by rw [he]; exact ⟨n, rfl⟩, rfl⟩
    rw [hset] at hle
    refine le_antisymm hle ?_
    -- the reverse: every ring element is measurable
    refine Real.sSup_le ?_ ?_
    · rintro r ⟨n, rfl⟩
      refine le_csSup (hbdd (Q x) inferInstance) ⟨e n, hCm _ (by rw [he]; exact ⟨n, rfl⟩), rfl⟩
    · refine le_csSup (hbdd (Q x) inferInstance) ⟨∅, MeasurableSet.empty, by simp⟩
  -- each term is measurable, and the family is uniformly bounded
  have hmeas : ∀ n : ℕ, Measurable (fun x => |((Q x) (e n)).toReal - (ν (e n)).toReal|) := by
    intro n
    have hAm : MeasurableSet (e n) := hCm _ (by rw [he]; exact ⟨n, rfl⟩)
    exact continuous_abs.measurable.comp
      (((Kernel.measurable_coe Q hAm).ennreal_toReal).sub measurable_const)
  have hbnd : ∀ x, BddAbove (Set.range fun n : ℕ => |((Q x) (e n)).toReal - (ν (e n)).toReal|) := by
    intro x
    refine ⟨2, ?_⟩
    rintro r ⟨n, rfl⟩
    have h1 : ((Q x) (e n)).toReal ≤ 1 := by
      refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
      simpa using prob_le_one
    have h2 : (ν (e n)).toReal ≤ 1 := by
      refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
      simpa using prob_le_one
    rw [abs_le]
    constructor <;>
      [linarith [ENNReal.toReal_nonneg (a := (Q x) (e n))];
       linarith [ENNReal.toReal_nonneg (a := ν (e n))]]
  simp only [hEq]
  exact Measurable.iSup hmeas
