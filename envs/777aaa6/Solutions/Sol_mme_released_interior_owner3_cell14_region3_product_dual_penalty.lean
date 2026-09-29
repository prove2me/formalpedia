-- Prove2me | solution 1 for mme_released_interior_owner3_cell14_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:51.871+00:00
-- url     : https://prove2.me/submissions/0b6084d2-62ce-457e-ac7a-d6c69106a62f

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 3 14 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(59834953241 / 100000000000), (74793773571 / 125000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (155943075433 / 1000000000000), (3824977148339 / 1000000000000), (3824978412657 / 1000000000000), (15594677031 / 100000000000)], ![(97250211203000000000000000000000000 / 1265436165369260491272844745775996841), (525722578007500000000000000000000000 / 3796308496107781473818534237327990523), (97250398212000000000000000000000000 / 1265436165369260491272844745775996841), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 3, -1, -1, 3], ![4, 3, 4, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-513580193429 / 1000000000000), (-513579096817 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-464566059849 / 250000000000), (134155249297 / 100000000000), (167694102939 / 125000000000), (-929120272961 / 500000000000)], ![(-2565884982243 / 1000000000000), (-1977010769793 / 1000000000000), (-2565883059277 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-128395048357 / 250000000000), (-32098693551 / 62500000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-371652847879 / 200000000000), (1341552492971 / 1000000000000), (1341552823513 / 1000000000000), (-1858240545921 / 1000000000000)], ![(-1282942491121 / 500000000000), (-15445396639 / 7812500000), (-641470764819 / 250000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-987541144323 / 200000000000), (-868955627773 / 500000000000), (-1149038139711 / 1000000000000), (-287259343409 / 250000000000), (-347582151947 / 200000000000), (-2468863197781 / 500000000000)] : List ℚ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-2468852860807 / 500000000000), (-347582251109 / 200000000000), (-114903813971 / 100000000000), (-229807474727 / 200000000000), (-868955379867 / 500000000000), (-4937726395561 / 1000000000000)] : List ℚ).getD
    ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 14) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 14 =>
        (splitWeight 3 14 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 14, ∏ i, weights i (c.val i) ≤ 1 := by
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
