-- Prove2me | solution 1 for UniversalRedundancy.SourceClass.isLeast_mAryError
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T17:09:46.14343+00:00
-- url     : https://prove2.me/submissions/dbc92d85-0375-42ec-9355-b1fbe8ec8cfc

import Definitions.Def_MachineLearning_TotalVariation_MultiHypothesis
import Definitions.Def_MachineLearning_TotalVariation_Testing
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X : Type*} [Fintype X] {Θ : Type*} [Fintype Θ] [Nonempty Θ] [DecidableEq Θ]
    (S : SourceClass X Θ) :
    IsLeast (Set.range S.mAryError) (1 - S.shtarkovSum / Fintype.card Θ) := by
  have hle1 : ∀ θ x, S.prob θ x ≤ 1 := by
    intro θ x
    rw [← S.sum_one θ]
    exact Finset.single_le_sum (f := fun x => S.prob θ x) (fun y _ => S.nonneg θ y) (Finset.mem_univ x)
  have hbdd : ∀ x, BddAbove (Set.range fun θ => S.prob θ x) := fun x =>
    ⟨1, by rintro _ ⟨θ, rfl⟩; exact hle1 θ x⟩
  have hle : ∀ θ x, S.prob θ x ≤ S.maxLik x := fun θ x => le_ciSup (hbdd x) θ
  have hml0 : ∀ x, 0 ≤ S.maxLik x := by
    intro x
    obtain ⟨θ₀⟩ := ‹Nonempty Θ›
    exact (S.nonneg θ₀ x).trans (hle θ₀ x)
  have hone_le : 1 ≤ S.shtarkovSum := by
    obtain ⟨θ₀⟩ := ‹Nonempty Θ›
    rw [← S.sum_one θ₀]
    exact Finset.sum_le_sum (fun x _ => hle θ₀ x)
  have hCpos : 0 < S.shtarkovSum := by linarith
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
  have hle_rule : ∀ T : X → Θ, ∑ x, S.prob (T x) x ≤ S.shtarkovSum :=
    fun T => Finset.sum_le_sum (fun x _ => hle (T x) x)
  refine ⟨⟨S.mlRule, ?_⟩, ?_⟩
  · rw [herr]
    congr 2
    unfold SourceClass.shtarkovSum
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hspec := (Finite.exists_max fun θ => S.prob θ x).choose_spec
    apply le_antisymm
    · exact hle _ x
    · exact ciSup_le hspec
  · rintro _ ⟨T, rfl⟩
    rw [herr]
    have := hle_rule T
    have h1 : (∑ x, S.prob (T x) x) / Fintype.card Θ ≤ S.shtarkovSum / Fintype.card Θ :=
      div_le_div_of_nonneg_right this hΘ.le
    linarith
