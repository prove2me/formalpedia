-- Prove2me | solution 1 for MarkovChainCLT.alphaMixingCoef_le_quarter
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T10:08:42.229563+00:00
-- url     : https://prove2.me/submissions/08fa04dd-70f3-48df-926a-ed09ead553c8

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-!
`α(n) ≤ 1/4`.  Each element of the defining set is `|c - a b|` with `a = P A`, `b = P B`,
`c = P (A ∩ B)`, and these satisfy `max (0, a + b - 1) ≤ c ≤ min (a, b)`; the elementary
consequence is `|c - a b| ≤ 1/4`.
-/

theorem solution {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E)
    (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    alphaMixingCoef P Y n ≤ 1 / 4 := by
  have hle : ∀ s : Set ℕ, processSigma Y s ≤ ‹MeasurableSpace Ω› :=
    fun s => iSup₂_le fun i _ => (hY i).comap_le
  have key : ∀ A B : Set Ω, MeasurableSet B →
      |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| ≤ 1 / 4 := by
    intro A B hB
    set a := (P A).toReal with ha
    set b := (P B).toReal with hb
    set c := (P (A ∩ B)).toReal with hc
    have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
    have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
    have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
    have ha1 : a ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ) (measure_mono (Set.subset_univ A))
    have hb1 : b ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ) (measure_mono (Set.subset_univ B))
    have hca : c ≤ a :=
      ENNReal.toReal_mono (measure_ne_top P A) (measure_mono Set.inter_subset_left)
    have hcb : c ≤ b :=
      ENNReal.toReal_mono (measure_ne_top P B) (measure_mono Set.inter_subset_right)
    have hunion : P A + P B = P (A ∪ B) + P (A ∩ B) := (measure_union_add_inter A hB).symm
    have hlow : a + b - 1 ≤ c := by
      have h1 : (P (A ∪ B)).toReal ≤ 1 := by
        simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
          (measure_mono (Set.subset_univ (A ∪ B)))
      have h2 : a + b = (P (A ∪ B)).toReal + c := by
        rw [ha, hb, hc, ← ENNReal.toReal_add (measure_ne_top P A) (measure_ne_top P B),
          ← ENNReal.toReal_add (measure_ne_top P (A ∪ B)) (measure_ne_top P (A ∩ B)), hunion]
      linarith
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1)]
    · nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1)]
  refine csSup_le ⟨0, ⟨0, ∅, ∅, @MeasurableSet.empty Ω (processSigma Y (Set.Iic 0)),
    @MeasurableSet.empty Ω (processSigma Y (Set.Ici (0 + n))), by simp⟩⟩ ?_
  rintro r ⟨k, A, B, -, hB, rfl⟩
  exact key A B (hle _ B hB)
