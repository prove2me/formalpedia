-- Prove2me | solution 2 for UniversalRedundancy.SourceClass.maxLik_eq_sum_prob_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T15:48:45.855701+00:00
-- url     : https://prove2.me/submissions/7fb6628e-6a4f-4e44-a040-b6ef95d4eec7

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ) [Fintype Θ] [Nonempty Θ]
    (x : X) :
    S.maxLik x = (∑ θ, S.prob θ x) ↔ ∀ θ θ' : Θ, θ ≠ θ' → S.prob θ x = 0 ∨ S.prob θ' x = 0 := by
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
  obtain ⟨θs, hθs⟩ : ∃ θs, S.maxLik x = S.prob θs x := by
    obtain ⟨θs, h⟩ := exists_eq_ciSup_of_finite (f := fun θ => S.prob θ x)
    exact ⟨θs, h.symm⟩
  constructor
  · intro h θ θ' hne
    by_contra hc
    push Not at hc
    have hp1 : 0 < S.prob θ x := lt_of_le_of_ne (S.nonneg θ x) (Ne.symm hc.1)
    have hp2 : 0 < S.prob θ' x := lt_of_le_of_ne (S.nonneg θ' x) (Ne.symm hc.2)
    obtain ⟨θ'', hne'', hp''⟩ : ∃ θ'', θ'' ≠ θs ∧ 0 < S.prob θ'' x := by
      by_cases hθ : θ = θs
      · exact ⟨θ', fun h' => hne (hθ.trans h'.symm), hp2⟩
      · exact ⟨θ, hθ, hp1⟩
    have hsum : S.prob θs x + S.prob θ'' x ≤ ∑ θ, S.prob θ x := by
      classical
      have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {θs, θ''})
        (fun i _ _ => S.nonneg i x) (f := fun θ => S.prob θ x)
      rwa [Finset.sum_pair hne''.symm] at this
    linarith
  · intro hs
    by_cases hall : ∀ θ, S.prob θ x = 0
    · simp only [hall, Finset.sum_const_zero]
      rw [hθs, hall]
    · push Not at hall
      obtain ⟨θ0, h0⟩ := hall
      have hzero : ∀ θ, θ ≠ θ0 → S.prob θ x = 0 := fun θ hθ => (hs θ θ0 hθ).resolve_right h0
      rw [Finset.sum_eq_single θ0 (fun θ _ hθ => hzero θ hθ) (by simp)]
      apply le_antisymm
      · refine ciSup_le (fun θ => ?_)
        by_cases hθ : θ = θ0
        · rw [hθ]
        · rw [hzero θ hθ]
          exact S.nonneg θ0 x
      · exact hle θ0 x
