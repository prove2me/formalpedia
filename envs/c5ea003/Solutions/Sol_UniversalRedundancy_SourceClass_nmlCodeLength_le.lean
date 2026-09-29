-- Prove2me | solution 1 for UniversalRedundancy.SourceClass.nmlCodeLength_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T15:31:30.894069+00:00
-- url     : https://prove2.me/submissions/a983f932-e4fd-48e0-9908-b17f3724d933

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ) [Nonempty Θ]
    (hpos : ∀ x, 0 < S.maxLik x) {θ : Θ} {x : X} (hp : 0 < S.prob θ x) :
    (S.nmlCodeLength x : ℝ) ≤ Real.logb 2 (1 / S.prob θ x) + Real.logb 2 S.shtarkovSum + 1 := by
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
  have hmlC : S.maxLik x ≤ S.shtarkovSum :=
    Finset.single_le_sum (f := fun y => S.maxLik y) (fun y _ => hml0 y) (Finset.mem_univ x)
  have hnml : 0 < S.nml x := div_pos (hpos x) hCpos
  have hnml1 : S.nml x ≤ 1 := (div_le_one hCpos).mpr hmlC
  have ht0 : 0 ≤ Real.logb 2 (1 / S.nml x) :=
    Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hnml]; linarith)
  have hceil : (S.nmlCodeLength x : ℝ) < Real.logb 2 (1 / S.nml x) + 1 := Nat.ceil_lt_add_one ht0
  have hmono : Real.logb 2 (1 / S.nml x) ≤ Real.logb 2 (1 / S.prob θ x) + Real.logb 2 S.shtarkovSum := by
    rw [← Real.logb_mul (by positivity) hCpos.ne']
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    unfold SourceClass.nml
    rw [one_div_div, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_left hCpos.le hp (hle θ x)
  linarith
