-- Prove2me | solution 2 for UniversalRedundancy.SourceClass.two_pow_neg_nmlCodeLength_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T15:27:29.633899+00:00
-- url     : https://prove2.me/submissions/c20e9fa2-ad0f-4383-b2c0-1dad34456397

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ) [Nonempty Θ]
    (hpos : ∀ x, 0 < S.maxLik x) (x : X) :
    (2 : ℝ) ^ (-(S.nmlCodeLength x : ℤ)) ≤ S.nml x := by
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
  have hnml : 0 < S.nml x := div_pos (hpos x) hCpos
  have hceil : Real.logb 2 (1 / S.nml x) ≤ (S.nmlCodeLength x : ℝ) := Nat.le_ceil _
  have h1 : (2 : ℝ) ^ (-(S.nmlCodeLength x : ℤ)) = (2 : ℝ) ^ (-(S.nmlCodeLength x : ℝ)) := by
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  rw [h1]
  calc (2 : ℝ) ^ (-(S.nmlCodeLength x : ℝ))
      ≤ (2 : ℝ) ^ (-(Real.logb 2 (1 / S.nml x))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = S.nml x := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
        field_simp
