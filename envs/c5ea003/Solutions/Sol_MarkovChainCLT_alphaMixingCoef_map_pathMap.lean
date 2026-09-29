-- Prove2me | solution 1 for MarkovChainCLT.alphaMixingCoef_map_pathMap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-05T19:27:40.424181+00:00
-- url     : https://prove2.me/submissions/4c0f4751-2e09-4208-88bc-749b92c044f3

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) (Y : ℕ → Ω → E) (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    alphaMixingCoef P Y n
      = alphaMixingCoef (Measure.map (fun ω i => Y i ω) P) (fun i (z : ℕ → E) => z i) n := by
  -- the path map and its measurability
  have hmap : Measurable (fun (ω : Ω) (i : ℕ) => Y i ω) :=
    measurable_pi_lambda _ (fun i => hY i)
  -- (1) coordinatewise: `σ(Y i) = Ŷ⁻¹ σ(coord i)`
  have hcomp : ∀ i : ℕ,
      MeasurableSpace.comap (Y i) (inferInstance : MeasurableSpace E)
        = MeasurableSpace.comap (fun (ω : Ω) (j : ℕ) => Y j ω)
            (MeasurableSpace.comap (fun z : ℕ → E => z i)
              (inferInstance : MeasurableSpace E)) :=
    fun i => (MeasurableSpace.comap_comp (m := (inferInstance : MeasurableSpace E))
      (f := fun z : ℕ → E => z i) (g := fun (ω : Ω) (j : ℕ) => Y j ω)).symm
  -- (2) the process σ-algebras are pullbacks of the coordinate σ-algebras
  have hsigma : ∀ s : Set ℕ, processSigma Y s
      = MeasurableSpace.comap (fun (ω : Ω) (i : ℕ) => Y i ω)
          (processSigma (fun i (z : ℕ → E) => z i) s) := by
    intro s
    show (⨆ i ∈ s, MeasurableSpace.comap (Y i) (inferInstance : MeasurableSpace E))
        = MeasurableSpace.comap (fun (ω : Ω) (i : ℕ) => Y i ω)
            (⨆ i ∈ s, MeasurableSpace.comap (fun z : ℕ → E => z i)
              (inferInstance : MeasurableSpace E))
    simp only [MeasurableSpace.comap_iSup, hcomp]
  -- (3) coordinate process σ-algebras sit inside the ambient product σ-algebra
  have hamb : ∀ (s : Set ℕ) {A : Set (ℕ → E)},
      MeasurableSet[processSigma (fun i (z : ℕ → E) => z i) s] A → MeasurableSet A := by
    intro s A hA
    have hle : processSigma (fun i (z : ℕ → E) => z i) s
        ≤ (inferInstance : MeasurableSpace (ℕ → E)) := by
      show (⨆ i ∈ s, MeasurableSpace.comap (fun z : ℕ → E => z i)
              (inferInstance : MeasurableSpace E)) ≤ _
      exact iSup₂_le fun i _ => (measurable_pi_apply i).comap_le
    exact hle A hA
  -- (4) the two defining sets of reals are literally equal
  unfold alphaMixingCoef
  congr 1
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, A, B, hA, hB, rfl⟩
    rw [hsigma] at hA hB
    obtain ⟨A', hA', rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    obtain ⟨B', hB', rfl⟩ := MeasurableSpace.measurableSet_comap.mp hB
    refine ⟨k, A', B', hA', hB', ?_⟩
    rw [Measure.map_apply hmap (hamb _ hA'), Measure.map_apply hmap (hamb _ hB'),
      Measure.map_apply hmap ((hamb _ hA').inter (hamb _ hB')), Set.preimage_inter]
  · rintro ⟨k, A, B, hA, hB, rfl⟩
    refine ⟨k, (fun (ω : Ω) (i : ℕ) => Y i ω) ⁻¹' A,
      (fun (ω : Ω) (i : ℕ) => Y i ω) ⁻¹' B, ?_, ?_, ?_⟩
    · rw [hsigma]; exact MeasurableSpace.measurableSet_comap.mpr ⟨A, hA, rfl⟩
    · rw [hsigma]; exact MeasurableSpace.measurableSet_comap.mpr ⟨B, hB, rfl⟩
    · rw [Measure.map_apply hmap (hamb _ hA), Measure.map_apply hmap (hamb _ hB),
        Measure.map_apply hmap ((hamb _ hA).inter (hamb _ hB)), Set.preimage_inter]
