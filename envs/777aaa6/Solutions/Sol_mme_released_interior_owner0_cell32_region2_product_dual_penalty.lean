-- Prove2me | solution 1 for mme_released_interior_owner0_cell32_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:06.457482+00:00
-- url     : https://prove2.me/submissions/2b968e54-5cb1-4a00-a8fc-d387530a2bc9

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 0 32 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(7805011628000000000000000000000000 / 3946525150676311705405236246247627037), (466560072974800000000000000000000000 / 3946525150676311705405236246247627037), (3326266946314200000000000000000000000 / 3946525150676311705405236246247627037), (466564122152200000000000000000000000 / 3946525150676311705405236246247627037), (7805012992000000000000000000000000 / 3946525150676311705405236246247627037)], ![(16148029811 / 40000000000), (845221208709 / 1000000000000), (403704278999 / 1000000000000), (1 / 1), (1 / 1)], ![(16819965191 / 40000000000), (778797110331 / 1000000000000), (84100608809 / 200000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 1, 2, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1245164943651 / 200000000000), (-427040795249 / 200000000000), (-42746211259 / 250000000000), (-2135195297491 / 1000000000000), (-1245164908699 / 200000000000)], ![(-453540702507 / 500000000000), (-168156900431 / 1000000000000), (-907072651727 / 1000000000000), (0 / 1), (0 / 1)], ![(-54144554317 / 62500000000), (-1953161843 / 7812500000), (-108287945061 / 125000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3112912359127 / 500000000000), (-533800994061 / 250000000000), (-34196969007 / 200000000000), (-213519529749 / 100000000000), (-3112912271747 / 500000000000)], ![(-907081405013 / 1000000000000), (-16815690043 / 100000000000), (-453536325863 / 500000000000), (0 / 1), (0 / 1)], ![(-866312869071 / 1000000000000), (-250004715903 / 1000000000000), (-866303560487 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-1999800232613 / 250000000000), (-792416102883 / 250000000000), (-658456274569 / 200000000000), (-1944369818061 / 1000000000000), (-58914646137 / 100000000000), (-972185179157 / 500000000000), (-658456277889 / 200000000000), (-3169665092603 / 1000000000000), (-7999218816967 / 1000000000000)] : List ℚ).getD
    ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-7999200930451 / 1000000000000), (-3169664411531 / 1000000000000), (-823070343211 / 250000000000), (-97218490903 / 50000000000), (-589146461369 / 1000000000000), (-1944370358313 / 1000000000000), (-823070347361 / 250000000000), (-1584832546301 / 500000000000), (-3999609408483 / 500000000000)] : List ℚ).getD
    ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 32) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 32 =>
        (splitWeight 0 32 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 32, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
