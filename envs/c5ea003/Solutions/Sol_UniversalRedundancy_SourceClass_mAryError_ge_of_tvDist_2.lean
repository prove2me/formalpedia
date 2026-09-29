-- Prove2me | solution 2 for UniversalRedundancy.SourceClass.mAryError_ge_of_tvDist
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T17:04:56.709668+00:00
-- url     : https://prove2.me/submissions/f2daa5be-6303-4d14-ad2e-2ce62f33680c

import Definitions.Def_MachineLearning_TotalVariation_MultiHypothesis
import Definitions.Def_MachineLearning_TotalVariation_Testing
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X : Type*} [Fintype X] {Θ : Type*} [Fintype Θ] [Nonempty Θ] [DecidableEq Θ]
    (S : SourceClass X Θ) (θ₀ : Θ) {ε : ℝ}
    (hε : ∀ θ, tvDist (S.prob θ) (S.prob θ₀) ≤ ε / Fintype.card Θ) (T : X → Θ) :
    1 - 1 / Fintype.card Θ - ε / Fintype.card Θ ≤ S.mAryError T := by
  have hΘ : (0 : ℝ) < Fintype.card Θ := by exact_mod_cast Fintype.card_pos
  have herr : ∀ T : X → Θ, S.mAryError T = 1 - (∑ x, S.prob (T x) x) / Fintype.card Θ := by
    intro T
    unfold SourceClass.mAryError
    have hsplit : ∀ θ, ∑ x ∈ Finset.univ.filter (fun x => T x ≠ θ), S.prob θ x
        = 1 - ∑ x ∈ Finset.univ.filter (fun x => T x = θ), S.prob θ x := by
      intro θ
      have h := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset X) (fun x => T x = θ) (S.prob θ)
      rw [S.sum_one θ] at h
      linarith
    have hfib : ∑ θ, ∑ x ∈ Finset.univ.filter (fun x => T x = θ), S.prob θ x = ∑ x, S.prob (T x) x := by
      rw [← Finset.sum_fiberwise (Finset.univ : Finset X) T (fun x => S.prob (T x) x)]
      refine Finset.sum_congr rfl (fun θ _ => Finset.sum_congr rfl (fun x hx => ?_))
      rw [(Finset.mem_filter.mp hx).2]
    simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, hfib]
    field_simp
  have hm : ∀ a : ℝ, max a 0 = (a + |a|) / 2 := by
    intro a
    rcases le_total a 0 with h | h
    · rw [max_eq_right h, abs_of_nonpos h]
      ring
    · rw [max_eq_left h, abs_of_nonneg h]
      ring
  have hpos_part : ∀ θ, ∑ x, max (S.prob θ x - S.prob θ₀ x) 0 = tvDist (S.prob θ) (S.prob θ₀) := by
    intro θ
    unfold tvDist
    simp only [hm]
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib, S.sum_one, S.sum_one]
    ring
  have hbound : ∑ x, S.prob (T x) x ≤ 1 + ε := by
    calc ∑ x, S.prob (T x) x
        ≤ ∑ x, (S.prob θ₀ x + ∑ θ, max (S.prob θ x - S.prob θ₀ x) 0) := by
          refine Finset.sum_le_sum (fun x _ => ?_)
          have h1 := le_max_left (S.prob (T x) x - S.prob θ₀ x) 0
          have h2 : max (S.prob (T x) x - S.prob θ₀ x) 0 ≤ ∑ θ, max (S.prob θ x - S.prob θ₀ x) 0 :=
            Finset.single_le_sum (f := fun θ => max (S.prob θ x - S.prob θ₀ x) 0)
              (fun θ _ => le_max_right _ _) (Finset.mem_univ (T x))
          linarith
      _ = 1 + ∑ θ, tvDist (S.prob θ) (S.prob θ₀) := by
          rw [Finset.sum_add_distrib, S.sum_one, Finset.sum_comm]
          simp only [hpos_part]
      _ ≤ 1 + ε := by
          have hs := Finset.sum_le_sum (fun θ (_ : θ ∈ Finset.univ) => hε θ)
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
          have he : (Fintype.card Θ : ℝ) * (ε / Fintype.card Θ) = ε := by
            field_simp
          linarith
  rw [herr]
  have h3 : (∑ x, S.prob (T x) x) / Fintype.card Θ ≤ (1 + ε) / Fintype.card Θ :=
    div_le_div_of_nonneg_right hbound hΘ.le
  have h4 : (1 + ε) / Fintype.card Θ = 1 / Fintype.card Θ + ε / Fintype.card Θ := by
    rw [add_div]
  linarith
